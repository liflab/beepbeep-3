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

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import ca.uqac.lif.bullwinkle.BnfParser;
import ca.uqac.lif.bullwinkle.BnfParser.InvalidGrammarException;
import ca.uqac.lif.bullwinkle.BnfRule;
import ca.uqac.lif.bullwinkle.ParseNode;
import ca.uqac.lif.bullwinkle.ParseNodeVisitor;
import ca.uqac.lif.cep.Buildable;
import ca.uqac.lif.cep.Combiner;
import ca.uqac.lif.cep.CountDecimate;
import ca.uqac.lif.cep.Delay;
import ca.uqac.lif.cep.Freeze;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Prefix;
import ca.uqac.lif.cep.Print;
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
	 * 
	 */
	protected Stack<Object> m_nodes;

	/**
	 * User-defined processors
	 */
	protected Map<String,GroupProcessor> m_processorDefinitions;

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
		m_nodes = new Stack<Object>();
		m_associations = new HashMap<String, Buildable>();
		m_processorDefinitions = new HashMap<String,GroupProcessor>();
		setBuiltinAssociations();
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
		addAssociation("<processor_def>", new ca.uqac.lif.cep.interpreter.UserDefinition());
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
	public void addAssociation(String production_rule, Buildable class_name)
	{
		m_associations.put(production_rule, class_name);
	}

	/**
	 * Resets the parser's internal state. Normally this should be
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
		String node_name = node.getToken();
		if (node_name == null)
		{
			// Nothing to do with that
			return;
		}
		if (node_name.startsWith("<"))
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

	public void setDebugMode(boolean b)
	{
		m_parser.setDebugMode(b);
	}

	protected void visitAssociation(ParseNode node)
	{
		// The node's name appears to refer to a Buildable object
		String node_name = node.getToken();
		Buildable obj = m_associations.get(node_name);
		Buildable b = obj.newInstance();
		b.build(m_nodes);
	}

	public void addProcessorDefinition(GroupProcessor pd)
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

	public Object parseLanguage(String property) throws ParseException
	{
		ParseNode node = null;
		try
		{
			node = m_parser.parse(property);
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
	
	public Object parseLanguage(String property, String start_symbol) throws ParseException
	{
		m_parser.setStartRule(start_symbol);
		return parseLanguage(property);
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

}
