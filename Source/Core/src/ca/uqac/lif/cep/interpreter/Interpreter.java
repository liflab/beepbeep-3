/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.interpreter;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import ca.uqac.lif.bullwinkle.BnfParser;
import ca.uqac.lif.bullwinkle.BnfParser.InvalidGrammarException;
import ca.uqac.lif.bullwinkle.BnfRule.InvalidRuleException;
import ca.uqac.lif.bullwinkle.BnfRule;
import ca.uqac.lif.bullwinkle.CaptureBlockParseNode;
import ca.uqac.lif.bullwinkle.ParseNode;
import ca.uqac.lif.bullwinkle.ParseNodeVisitor;
import ca.uqac.lif.cep.Buildable;
import ca.uqac.lif.cep.Combiner;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.CountDecimate;
import ca.uqac.lif.cep.Delay;
import ca.uqac.lif.cep.Fork;
import ca.uqac.lif.cep.Freeze;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Passthrough;
import ca.uqac.lif.cep.Prefix;
import ca.uqac.lif.cep.Print;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.QueueSource;
import ca.uqac.lif.cep.Window;
import ca.uqac.lif.util.EmptyException;
import ca.uqac.lif.util.PackageFileReader;

public class Interpreter implements ParseNodeVisitor
{
	/**
	 * Location of the file containing the grammar. This path is
	 * relative to the location of the <tt>Interpreter</tt> class
	 */
	protected static String s_grammarFile = "epl.bnf";

	/**
	 * The parser used to read expressions
	 */
	protected BnfParser m_parser;

	/**
	 * The stack used to build the object resulting from the parsing  
	 */
	protected GroupStack<Object> m_nodes;
	
	/**
	 * A counter so that every user definition number is unique
	 */
	protected static int s_defNb = 0;
	
	/**
	 * The result of the last call to the interpreter. This either
	 * stores a user definition, a processor, or null if the interpretation
	 * failed.
	 */
	protected Object m_lastQuery = null;

	/**
	 * User-defined processors
	 */
	protected Map<String, GroupProcessor> m_processorDefinitions;
	
	/**
	 * Forks
	 */
	protected Map<String, Fork> m_processorForks;
	
	/**
	 * User-defined objects
	 */
	protected Map<String, Object> m_symbolDefinitions;

	/**
	 * Associations between the name of a production rule and
	 * the buildable object whose syntax it defines
	 */
	protected Map<String, Buildable> m_associations;
	
	/**
	 * Instantiates an interpreter and prepares it to parse expressions
	 */
	public Interpreter()
	{
		super();
		m_parser = initializeParser();
		m_nodes = new GroupStack<Object>();
		m_associations = new HashMap<String, Buildable>();
		m_processorDefinitions = new HashMap<String, GroupProcessor>();
		m_symbolDefinitions = new HashMap<String, Object>();
		m_processorForks = new HashMap<String, Fork>();
		setBuiltinAssociations();
	}
	
	/**
	 * Instantiates an interpreter with the rules of another
	 * @param i The interpreter to borrow the rules form
	 */
	public Interpreter(Interpreter i)
	{
		super();
		m_parser = new BnfParser(i.m_parser);
		m_nodes = new GroupStack<Object>();
		m_nodes.addAll(i.m_nodes);
		m_associations = new HashMap<String,Buildable>();
		m_associations.putAll(i.m_associations);
		m_processorDefinitions = new HashMap<String,GroupProcessor>();
		m_processorDefinitions.putAll(i.m_processorDefinitions);
		m_symbolDefinitions = new HashMap<String, Object>();
		m_symbolDefinitions.putAll(i.m_symbolDefinitions);
		m_processorForks = new HashMap<String, Fork>();
		m_processorForks.putAll(i.m_processorForks);
	}
	
	/**
	 * Extends the interpreter's grammar with new definitions
	 * @param c A grammar extension class to add to the interpreter
	 */
	public void extendGrammar(Class<? extends GrammarExtension> c)
	{
		try 
		{
			GrammarExtension ext = c.newInstance();
			extendGrammar(ext);
		} 
		catch (InstantiationException e) 
		{
			e.printStackTrace();
		} 
		catch (IllegalAccessException e) 
		{
			e.printStackTrace();
		}
	}
	
	/**
	 * Extends the interpreter's grammar with new definitions
	 * @param ext The grammar extension to add to the interpreter
	 */
	public void extendGrammar(GrammarExtension ext)
	{
		// Adds the associations
		Map<String,Buildable> associations = ext.getAssociations();
		m_associations.putAll(associations);
		// Adds the productions
		String productions = ext.getGrammar();
		try
		{
			m_parser.setGrammar(productions);
		}
		catch (InvalidGrammarException e)
		{
			e.printStackTrace();
		}
	}

	protected void setBuiltinAssociations()
	{
		// Basic
		addAssociation("<p_combiner>", new Combiner());
		addAssociation("<p_constant>", new QueueSource());
		addAssociation("<p_decimate>", new CountDecimate());
		addAssociation("<p_delay>", new Delay());
		addAssociation("<p_freeze>", new Freeze());
		//addAssociation("<p_function>", new Function());
		addAssociation("<p_prefix>", new Prefix());
		addAssociation("<p_print>", new Print());
		addAssociation("<p_window>", new Window());
		
		// User definitions
		addAssociation("<processor_def>", new UserDefinition());
		addAssociation("<symbol_def_list>", new ca.uqac.lif.cep.interpreter.SymbolDefinitionList());
		addAssociation("<symbol_def>", new ca.uqac.lif.cep.interpreter.SymbolDefinition());

		// Math
		/* This will be moved to the tuple EML
		addAssociation("<f_addition>", "ca.uqac.lif.cep.math.Addition");
		addAssociation("<f_subtraction>", "ca.uqac.lif.cep.math.Subtraction");
		addAssociation("<f_division>", "ca.uqac.lif.cep.math.Division");
		addAssociation("<f_power>", "ca.uqac.lif.cep.math.Power");
		addAssociation("<c_sum>", "ca.uqac.lif.cep.math.Sum");
		*/
	}

	/**
	 * Associates a production rule name to a processor
	 * @param production_rule The rule name
	 * @param p The processor
	 */
	void addAssociation(String production_rule, Buildable class_name)
	{
		m_associations.put(production_rule, class_name);
	}
	
	public void addSymbolDefinition(String symbol_name, Buildable object)
	{
		m_symbolDefinitions.put(symbol_name, object);
	}
	
	public void addSymbolDefinitions(Map<String, Buildable> defs)
	{
		m_symbolDefinitions.putAll(defs);
	}
	
	public void addPlaceholder(String symbol_name, String non_terminal, Buildable object)
	{
		m_symbolDefinitions.put(symbol_name, object);
		try
		{
			BnfRule rule = BnfRule.parseRule("<" + non_terminal + "> := " + symbol_name);
			m_parser.addRule(rule);
		}
		catch (InvalidRuleException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/**
	 * Resets the interpreter's internal state. Normally this should be
	 * called before parsing each new expression.
	 */
	public void reset()
	{
		m_nodes.clear();
	}

	/**
	 * Initializes the BNF parser
	 * @return The initialized BNF parser
	 */
	protected BnfParser initializeParser()
	{
		BnfParser parser = new BnfParser();
		String grammar = null;
		try
		{
			grammar = getGrammarString();
			parser.setGrammar(grammar);
		} 
		catch (InvalidGrammarException e)
		{
			e.printStackTrace();
		}
		//parser.setDebugMode(true);
		return parser;
	}

	/**
	 * Retrieves the grammar from the file
	 * @return The grammar
	 */
	protected static String getGrammarString()
	{
		return PackageFileReader.readPackageFile(Interpreter.class, s_grammarFile);
	}

	@Override
	public void visit(ParseNode node)
	{
		if (node instanceof CaptureBlockParseNode)
		{
			// Do nothing with these nodes at the moment
			return;
		}
		String node_name = node.getToken();
		if (node_name == null)
		{
			// Nothing to do with that
			return;
		}
		if (node_name.startsWith("@") && m_symbolDefinitions.containsKey(node_name))
		{
			// This is a placeholder for some grammatical element:
			// fetch the object this symbol stands for...
			Object o = m_symbolDefinitions.get(node_name);
			if (o instanceof Processor)
			{
				// In the case of processors, we must fork their output
				Processor o_p = (Processor) o;
				if (!m_processorForks.containsKey(node_name))
				{
					Fork f = new Fork(0);
					Connector.connect(o_p, f, 0, 0);
					m_processorForks.put(node_name, f);
				}
				// Extend the current fork for this processor with a new output
				Fork f = m_processorForks.get(node_name);
				int new_arity = f.getOutputArity() + 1;
				f.extendArity(new_arity);
				Passthrough pt = new Passthrough(o_p.getOutputArity());
				Connector.connect(f, pt, new_arity - 1, 0);
				m_nodes.push(pt);
			}
			else
			{
				// ...and replace the symbol by this object on the stack
				//m_nodes.pop();
				m_nodes.push(o);
			}
		}
		else if (node_name.startsWith("<"))
		{
			// Production rule
			if (m_associations.containsKey(node_name))
			{
				// Production rule for something buildable from stack contents
				visitAssociation(node);
			}
		}
		else
		{
			// Try to interpret node as a number
			boolean is_number = false;
			try
			{
				Number n = Float.parseFloat(node_name);
				m_nodes.push(n);
				is_number = true;
			}
			catch (Exception e)
			{
				// Do nothing; this only means we can't parse the string
				// as a number
			}
			if (!is_number)
			{
				// It's not a number: then it's a string
				if (node_name.startsWith("\""))
				{
					// Remove quotes if any
					node_name = node_name.replaceAll("\"", "");
				}
				m_nodes.push(node_name);
			}
		}
	}

	protected void visitAssociation(ParseNode node)
	{
		// The node's name appears to refer to a Buildable object
		String node_name = node.getToken();
		Buildable obj = m_associations.get(node_name);
		Buildable b = obj.newInstance();
		b.build(m_nodes);
	}

	void addProcessorDefinition(GroupProcessor pd)
	{
		// Add rules to the parser
		String rule_name = "USERDEFPROC" + pd.getId(); // So that each definition is unique
		pd.setRuleName(rule_name);
		BnfRule rule = pd.getRule();
		m_parser.addRule(rule);
		m_parser.addCaseToRule("<userdef_proc>", "<" + rule_name + ">");
		// Add definition
		m_processorDefinitions.put(rule_name, pd);
	}

	@Override
	public void pop()
	{
		// Nothing to do
	}
	
	public Pullable executeQuery(String query)
	{
		return executeQuery(query, 0);
	}
	
	public Pullable executeQuery(String query, int index)
	{
		Object result;
		try 
		{
			result = parseQuery(query);
			m_lastQuery = result;
			if (result instanceof Processor)
			{
				Pullable out = ((Processor) result).getPullableOutput(index);
				return out;
			}
			else if (result instanceof UserDefinition)
			{
				((UserDefinition) result).addToInterpreter();
				return null;
			}
		} 
		catch (ParseException e) 
		{
			System.err.println("Error parsing expression " + query);
			e.printStackTrace();
		}
		return null;
	}
	
	public Pullable executeQueries(InputStream is) throws IOException
	{
		BufferedReader in = new BufferedReader(new InputStreamReader(is));
		String input_line;
		StringBuilder contents = new StringBuilder();
		while ((input_line = in.readLine()) != null)
		{
			contents.append(input_line).append("\n");
		}
		in.close();
		return executeQueries(contents.toString());
	}
	
	public Pullable executeQueries(String queries)
	{
		queries += "\n"; // Apppend a CR so that the last query is also matched
		queries = queries.replaceAll("--.*?\n", "\n");
		String[] parts = queries.split("\\.\n");
		Pullable last = null;
		for (String query : parts)
		{
			query = query.replaceAll("\\s+", " ");
			query = query.trim();
			if (!query.isEmpty())
			{
				last = executeQuery(query);
			}
		}
		return last;
	}

	public Object parseQuery(String query) throws ParseException
	{
		ParseNode node = null;
		try
		{
			node = m_parser.parse(query);
		}
		catch (BnfParser.ParseException e)
		{
			throw new ParseException(e.toString());
		}
		if (node != null)
		{
			return parseStatement(node);
		}
		else
		{
			throw new ParseException("Error: the BNF parser returned null");
		}
		//return null;    
	}
	
	protected Object parseLanguage(String property, String start_symbol) throws ParseException
	{
		m_parser.setStartRule(start_symbol);
		return parseQuery(property);
	}

	protected Object parseStatement(ParseNode root)
	{
		reset();
		root.postfixAccept(this);
		if (m_nodes.isEmpty())
		{
			return null;
		}
		return m_nodes.peek();
	}
	
	void addCaseToRule(String rule_name, String case_string)
	{
		m_parser.addCaseToRule(rule_name, case_string);
	}
	
	void addRule(BnfRule rule)
	{
		m_parser.addRule(rule);
	}

	public static class ParseException extends EmptyException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		public ParseException(String message)
		{
			super(message);
		}
	}

	public static class NoSuchProcessorException extends ParseException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		public NoSuchProcessorException(String message)
		{
			super(message);
		}
	}
	
	class UserDefinition implements Buildable 
	{
		/**
		 * The definition of each variable occurring in the expression 
		 */
		protected SymbolDefinitionList m_symbolDefs;
		
		/**
		 * The non-terminal symbol of the grammar this definition adds 
		 * a new case to
		 */
		protected String m_symbolName;
		
		/**
		 * The definition
		 */
		protected String m_definition;
		
		/**
		 * The parsing pattern
		 */
		protected String m_pattern;
		
		/**
		 * An interpreter to parse the definition
		 */
		protected Interpreter m_interpreter;
		
		/**
		 * The object (processor, constant, etc.) this definition ultimately
		 * stands for
		 */
		protected Object m_standsFor;
		
		public UserDefinition()
		{
			super();
		}
		
		void setInterpreter(Interpreter i)
		{
			m_interpreter = i;
		}

		@Override
		public void build(Stack<Object> stack) 
		{
			// We use toString: if the definition is a single number, a number is
			// on the stack rather than a string
			m_definition = ((String) stack.pop().toString()).trim();
			m_symbolName = ((String) stack.pop()).trim();
			stack.pop(); // THE
			stack.pop(); // IS
			m_pattern = ((String) stack.pop()).trim();
			if (!stack.isEmpty())
			{
				Object separator = stack.pop();
				if (separator instanceof String && ((String) separator).compareTo(":") == 0)
				{
					// This is a definition with a context
					m_symbolDefs = (SymbolDefinitionList) stack.pop();
					stack.pop(); // WHEN
				}
			}
			stack.push(this);
		}
		
		Object parseDefinition(Map<String,Buildable> symbol_defs)
		{
			Interpreter inner_int = new Interpreter(Interpreter.this);
			inner_int.addSymbolDefinitions(symbol_defs);
			int in_arity = 0;
			for (String symbol : symbol_defs.keySet())
			{
				Object def = symbol_defs.get(symbol);
				if (def instanceof Processor)
				{
					in_arity++;
				}
			}
			if (m_symbolDefs != null && !m_symbolDefs.isEmpty())
			{
				for (String symbol : m_symbolDefs.keySet())
				{
					String symbol_nonterminal = m_symbolDefs.get(symbol);
					try 
					{
						BnfRule rule = BnfRule.parseRule("<" + symbol_nonterminal + "> := " + symbol);
						inner_int.addRule(rule);
					} 
					catch (InvalidRuleException e) 
					{
						e.printStackTrace();
					}
				}
			}
			Object parsed = null;
			try 
			{
				//inner_int.setDebugMode(true);
				// We give a hint to the interpreter by telling it what
				// non-terminal symbol to start parsing from
				parsed = inner_int.parseLanguage(m_definition, "<" + m_symbolName + ">");
			} 
			catch (ParseException e) 
			{
				e.printStackTrace();
			}
			if (parsed != null && parsed instanceof Processor && m_symbolName.compareTo("processor") == 0)
			{
				// The parsing succeeded: create a group processor out of 
				// the parsed expression
				Processor p_parsed = (Processor) parsed;
				GroupProcessor gp = new GroupProcessor(in_arity, p_parsed.getOutputArity());
				gp.addProcessor(p_parsed);
				int i = 0;
				for (Object o : inner_int.m_nodes.getHistory())
				{
					if (o instanceof Processor)
					{
						gp.addProcessor((Processor) o);
					}
				}
				for (String placeholder : inner_int.m_processorForks.keySet())
				{
					Fork f = inner_int.m_processorForks.get(placeholder);
					//gp.addProcessor(f);
					gp.associateInput(i, f, 0);
				}
				for (int j = 0; j < p_parsed.getOutputArity(); j++)
				{
					gp.associateOutput(j, p_parsed, j);
				}
				return gp;
			}
			return parsed;
		}
		
		/**
		 * Adds this user definition to the grammar of an existing interpreter
		 */
		public void addToInterpreter()
		{
			String pattern = createPattern();
			String non_terminal = "<USERDEF" + s_defNb++ + ">";
			try 
			{
				addRule(BnfRule.parseRule(non_terminal + " := " + pattern));
			} 
			catch (InvalidRuleException e) 
			{
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			addCaseToRule("<" + m_symbolName + ">", non_terminal);
			addAssociation(non_terminal, new UserDefinitionInstance(this));
		}
		
		/**
		 * Creates a new grammar case that matches the pattern declared for this
		 * definition. For example, given the expression:
		 * <pre>
		 * WHEN @P IS A XYZ: THE COUNT OF @P IS THE ABC ...
		 * </pre>
		 * This would create the following case, appended to the cases of
		 * non-terminal symbol ABC:
		 * <pre>
		 * THE COUNT OF &lt;XYZ&gt;
		 * </pre>
		 * @return A string containing the new grammar case
		 */
		protected String createPattern()
		{
			String out = new String(m_pattern);
			if (m_symbolDefs != null && !m_symbolDefs.isEmpty())
			{
				for (String var_name : m_symbolDefs.keySet())
				{
					out = out.replaceAll(var_name, "<" + m_symbolDefs.get(var_name) + ">");
				}
			}
			return out;
		}
		
		@Override
		public String toString()
		{
			StringBuilder out = new StringBuilder();
			out.append("WHEN ").append(m_symbolDefs).append(": ");
			out.append(m_pattern).append(" IS THE ").append(m_symbolName);
			out.append(" ").append(m_definition).append(".");
			return out.toString();
		}
		
		@Override
		public UserDefinition newInstance()
		{
			UserDefinition out = new UserDefinition();
			out.m_definition = m_definition;
			out.m_pattern = m_pattern;
			out.m_standsFor = m_standsFor;
			out.m_symbolDefs = m_symbolDefs;
			out.m_symbolName = m_symbolName;
			return out;
		}
	}
	
	/**
	 * Returns the result of the last call to the interpreter.
	 * This is either a processor, a user definition, or null if the
	 * interpreter failed, depending on the query.
	 * @return The result of the call
	 */
	public Object getLastQuery()
	{
		return m_lastQuery;
	}
}
