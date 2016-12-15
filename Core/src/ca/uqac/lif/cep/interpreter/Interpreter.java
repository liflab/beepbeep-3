/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.interpreter;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.logging.Level;

import ca.uqac.lif.bullwinkle.BnfParser;
import ca.uqac.lif.bullwinkle.BnfParser.InvalidGrammarException;
import ca.uqac.lif.bullwinkle.BnfRule;
import ca.uqac.lif.bullwinkle.BnfRule.InvalidRuleException;
import ca.uqac.lif.bullwinkle.CaptureBlockParseNode;
import ca.uqac.lif.bullwinkle.ParseNode;
import ca.uqac.lif.bullwinkle.ParseNodeVisitor;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Palette;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.io.LineReader;
import ca.uqac.lif.cep.io.StreamReader;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.SmartFork;
import ca.uqac.lif.cep.util.BeepBeepLogger;
import ca.uqac.lif.cep.util.PackageFileReader;

public class Interpreter implements ParseNodeVisitor
{
	/**
	 * Location of the file containing the grammar. This path is
	 * relative to the location of the <tt>Interpreter</tt> class
	 */
	protected static String s_grammarFile = "eml.bnf";

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
	 * The system-dependent line separator
	 */
	public static final String CRLF = System.getProperty("line.separator");

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
	protected Map<String, SmartFork> m_processorForks;

	/**
	 * User-defined objects
	 */
	protected Map<String, Object> m_symbolDefinitions;

	/**
	 * Associations between the name of a production rule and
	 * the buildable <em>instance</em> whose syntax it defines
	 */
	protected Map<String, Object> m_userDefinedAssociations;

	/**
	 * Associations between the name of a production rule and
	 * the buildable class whose syntax it defines
	 */
	protected Map<String, Class<?>> m_associations;

	/**
	 * A set of exceptions encountered when parsing the expressions
	 */
	protected Set<Exception> m_lastExceptions;

	/**
	 * Instantiates an interpreter and prepares it to parse expressions
	 */
	public Interpreter()
	{
		super();
		// Initialize empty containers
		m_parser = initializeParser();
		m_nodes = new GroupStack<Object>();
		m_associations = new HashMap<String, Class<?>>();
		m_userDefinedAssociations = new HashMap<String,Object>();
		m_processorDefinitions = new HashMap<String, GroupProcessor>();
		m_symbolDefinitions = new HashMap<String, Object>();
		m_processorForks = new HashMap<String, SmartFork>();
		m_lastExceptions = new HashSet<Exception>();
		// Load boostrap grammar
		load(BootstrapGrammar.class);
		m_parser.setStartRule("<S>");
		// Load built-in extensions
		load(ca.uqac.lif.cep.tmf.PackageExtension.class);
		load(ca.uqac.lif.cep.functions.PackageExtension.class);
		load(ca.uqac.lif.cep.numbers.PackageExtension.class);
		load(ca.uqac.lif.cep.io.PackageExtension.class);
		//extendGrammar(ca.uqac.lif.cep.sets.PackageExtension.class);
	}

	/**
	 * Creates an instance of an ESQL interpreter by loading a number of
	 * extensions.
	 * <p>
	 * Note: we must resort to this signature, rather than the natural
	 * <tt>Class&lt;? extends GrammarExtension&gt; ...</tt> that we would normally
	 * write. The reason is backwards compatibility with Java 1.6.
	 * Using Java &gt; 1.6 would require us to add the @SafeVarargs
	 * annotation to prevent compile warnings, but this annotation
	 * does not exist in Java 1.6 and produces a compile error. Thus this
	 * is the only way to ensure warning- and error-free compilation in
	 * both situations.
	 * @param extensions A list of extensions to load into the interpreter
	 * @return An instance of the interpreter
	 */
	@SuppressWarnings("unchecked")
	public static Interpreter newInterpreter(Class<?> ... extensions)
	{
		Interpreter interp = new Interpreter();
		for (Class<?> pal_class : extensions)
		{
			if (pal_class.isAssignableFrom(Palette.class))
			{
				interp.load((Class<? extends Palette>) pal_class);
			}
		}
		return interp;
	}

	/**
	 * Creates a {@link ca.uqac.lif.cep.io.StreamReader StreamReader} from
	 * an input stream, and associates it to a placeholder in the
	 * interpreter's grammar. This allows the interpreter to refer to
	 * external input sources by a name in its queries.
	 * <p>
	 * An example usage would be:
	 * <pre>
	 * FileInputStream fis = new FileInputStream(new File("bar.txt"));
	 * my_interpreter.nameInputStream("@foo", fis);
	 * </pre>
	 * From this point on, writing "@foo" in a query will refer to a
	 * {@link ca.uqac.lif.cep.io.StreamReader StreamReader} reading from
	 * external file "bar.txt".
	 * 
	 * @param name The name of the placeholder
	 * @param is The <code>InputStream</code> to read from
	 * @return This interpreter
	 */
	public Interpreter addStreamReader(String name, InputStream is)
	{
		StreamReader sr = new StreamReader(is);
		addPlaceholder(name, "processor", sr);
		return this;
	}

	/**
	 * Like {@link #addStreamReader(String, InputStream) addStreamReader()},
	 * but creates a {@link ca.uqac.lif.cep.io.LineReader LineReader} instead.
	 * 
	 * @param name The name of the placeholder
	 * @param is The <code>InputStream</code> to read from
	 * @return This interpreter
	 */
	public Interpreter addLineReader(String name, InputStream is)
	{
		LineReader sr = new LineReader(is);
		sr.addCrlf(false);
		addPlaceholder(name, "processor", sr);
		return this;
	}

	/**
	 * Instantiates an interpreter, specifying a list of grammar extensions
	 * to load.
	 * <p>
	 * Note: we must resort to this signature, rather than the natural
	 * <tt>Class&lt;? extends GrammarExtension&gt; ...</tt> that we would normally
	 * write. The reason is backwards compatibility with Java 1.6.
	 * Using Java &gt; 1.6 would require us to add the @SafeVarargs
	 * annotation to prevent compile warnings, but this annotation
	 * does not exist in Java 1.6 and produces a compile error. Thus this
	 * is the only way to ensure warning- and error-free compilation in
	 * both situations.
	 * @param extensions The list of grammar extensions to load into
	 *   the interpreter
	 */
	@SuppressWarnings("unchecked")
	public Interpreter(Class<?>  ... extensions)
	{
		this();
		for (Class<?> ext : extensions)
		{
			if (ext.isAssignableFrom(Palette.class))
			{
				load((Class<? extends Palette>) ext);
			}
		}
	}

	/**
	 * Instantiates an interpreter with the rules of another
	 * @param i The interpreter to borrow the rules form
	 */
	public Interpreter(Interpreter i)
	{
		super();
		m_parser = new BnfParser(i.m_parser);
		m_lastExceptions = new HashSet<Exception>();
		m_nodes = new GroupStack<Object>();
		m_nodes.addAll(i.m_nodes);
		m_associations = new HashMap<String,Class<?>>();
		m_associations.putAll(i.m_associations);
		m_userDefinedAssociations = new HashMap<String,Object>();
		m_userDefinedAssociations.putAll(i.m_userDefinedAssociations);
		m_processorDefinitions = new HashMap<String,GroupProcessor>();
		m_processorDefinitions.putAll(i.m_processorDefinitions);
		m_symbolDefinitions = new HashMap<String, Object>();
		m_symbolDefinitions.putAll(i.m_symbolDefinitions);
		m_processorForks = new HashMap<String, SmartFork>();
		m_processorForks.putAll(i.m_processorForks);
	}

	/**
	 * Extends the interpreter's grammar with new definitions
	 * @param c A grammar extension class to add to the interpreter
	 * @return This interpreter
	 */
	public Interpreter load(Class<? extends Palette> c)
	{
		try
		{
			Palette ext = c.newInstance();
			load(ext);
		}
		catch (InstantiationException e)
		{
			BeepBeepLogger.logger.log(Level.SEVERE, "", e);
		}
		catch (IllegalAccessException e)
		{
			BeepBeepLogger.logger.log(Level.SEVERE, "", e);
		}
		return this;
	}

	/**
	 * Extends the interpreter's grammar with new definitions
	 * @param ext The grammar extension to add to the interpreter
	 * @return This interpreter
	 */
	public Interpreter load(Palette ext)
	{
		// Adds the associations
		Map<String,Class<?>> associations = ext.getAssociations();
		m_associations.putAll(associations);
		// Adds the productions
		String productions = ext.getGrammar();
		try
		{
			m_parser.setGrammar(productions);
		}
		catch (InvalidGrammarException e)
		{
			BeepBeepLogger.logger.log(Level.SEVERE, "", e);
		}
		return this;
	}

	/**
	 * Associates a production rule name to a processor
	 * @param production_rule The rule name
	 * @param p The processor
	 */
	void addAssociation(String production_rule, Class<?> c)
	{
		m_associations.put(production_rule, c);
	}

	/**
	 * Associates a production rule name to a processor
	 * @param production_rule The rule name
	 * @param p The processor
	 */
	void addUserDefinedAssociation(String production_rule, Object o)
	{
		m_userDefinedAssociations.put(production_rule, o);
	}

	public void addSymbolDefinition(String symbol_name, Object object)
	{
		m_symbolDefinitions.put(symbol_name, object);
	}

	public void addSymbolDefinitions(Map<String, Object> defs)
	{
		m_symbolDefinitions.putAll(defs);
	}

	public void addPlaceholder(String symbol_name, String non_terminal, Object object)
	{
		m_symbolDefinitions.put(symbol_name, object);
		try
		{
			BnfRule rule = BnfRule.parseRule("<" + non_terminal + "> := " + symbol_name);
			m_parser.addRule(0, rule);
		}
		catch (InvalidRuleException e)
		{
			BeepBeepLogger.logger.log(Level.SEVERE, "", e);
		}
	}

	/**
	 * Resets the interpreter's internal state. Normally this should be
	 * called before parsing each new expression.
	 */
	public void reset()
	{
		m_nodes.clear();
		m_lastExceptions.clear();
	}

	/**
	 * Initializes the BNF parser
	 * @return The initialized BNF parser
	 */
	protected BnfParser initializeParser()
	{
		BnfParser parser = new BnfParser();
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
					SmartFork f = new SmartFork(0);
					try
					{
						Connector.connect(o_p, f, 0, 0);
					}
					catch (ConnectorException e)
					{
						m_lastExceptions.add(e);
					}
					m_processorForks.put(node_name, f);
				}
				// Extend the current fork for this processor with a new output
				SmartFork f = m_processorForks.get(node_name);
				int new_arity = f.getOutputArity() + 1;
				Passthrough pt = new Passthrough(o_p.getOutputArity());
				/*
				Fork new_f = new Fork(new_arity, f);
				Connector.connect(new_f, pt, new_arity - 1, 0);
				m_processorForks.put(node_name, new_f);
				 */
				f.extendOutputArity(new_arity);
				try
				{
					Connector.connect(f, pt, new_arity - 1, 0);
				}
				catch (ConnectorException e)
				{
					m_lastExceptions.add(e);
				}
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
				try
				{
					visitAssociation(node);
				}
				catch (IllegalAccessException e)
				{
					m_lastExceptions.add(e);
				}
				catch (IllegalArgumentException e)
				{
					m_lastExceptions.add(e);
				}
				catch (PipingParseException e)
				{
					m_lastExceptions.add(e);
				}
			}
			else if (m_userDefinedAssociations.containsKey(node_name))
			{
				// Production rule for something buildable from stack contents
				visitUserDefinedAssociation(node);
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
			catch (NumberFormatException e)
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

	protected void visitAssociation(ParseNode node) throws IllegalAccessException, IllegalArgumentException, PipingParseException
	{
		// The node's name appears to refer to a Buildable object
		String node_name = node.getToken();
		Class<?> obj = m_associations.get(node_name);
		Method m = getStaticMethod(obj, "build", Stack.class);
		if (m == null)
		{
			throw new IllegalAccessException("Method build does not exist in class " + obj);
		}
		m.setAccessible(true);
		try
		{
			m.invoke(null, m_nodes);
		}
		catch (InvocationTargetException e)
		{
			Throwable th = e.getTargetException();
			if (th instanceof Exception)
			{
				m_lastExceptions.add((Exception) th);
			}
			BeepBeepLogger.logger.log(Level.WARNING, "", e);
		}
	}

	protected void visitUserDefinedAssociation(ParseNode node)
	{
		// The node's name appears to refer to a Buildable object
		String node_name = node.getToken();
		Object obj = m_userDefinedAssociations.get(node_name);
		Method m = getMethod(obj, "build", Stack.class);
		try
		{
			m.invoke(obj, m_nodes);
		}
		catch (IllegalAccessException e)
		{
			BeepBeepLogger.logger.throwing("Interpreter", "visitUserDefinedAssociation", e);
		}
		catch (IllegalArgumentException e)
		{
			BeepBeepLogger.logger.throwing("Interpreter", "visitUserDefinedAssociation", e);
		}
		catch (InvocationTargetException e)
		{
			Throwable th = e.getTargetException();
			if (th instanceof Exception)
			{
				m_lastExceptions.add((Exception) th);
			}
			BeepBeepLogger.logger.log(Level.WARNING, "", e);
		}
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

	public Pullable executeQuery(String query) throws ParseException
	{
		return executeQuery(query, 0);
	}

	public Pullable executeQuery(String query, int index) throws ParseException
	{
		Object result;
		result = parseQuery(query);
		m_lastQuery = result;
		if (result instanceof Processor)
		{
			Pullable out = ((Processor) result).getPullableOutput(index);
			return out;
		}
		else if (result instanceof UserDefinition)
		{
			UserDefinition ud = (UserDefinition) result;
			ud.addToInterpreter(this);
			return null;
		}
		return null;
	}

	public Pullable executeQueries(InputStream is) throws ParseException, IOException
	{
		BufferedReader in = new BufferedReader(new InputStreamReader(is));
		String input_line;
		StringBuilder contents = new StringBuilder();
		while ((input_line = in.readLine()) != null)
		{
			contents.append(input_line).append(CRLF);
		}
		in.close();
		return executeQueries(contents.toString());
	}

	public Pullable executeQueries(String queries) throws ParseException
	{
		queries += CRLF; // Apppend a CR so that the last query is also matched
		queries = queries.replaceAll("--.*?" + CRLF, CRLF);
		String[] parts = queries.split("\\." + CRLF);
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

	public Object parseQueryLifted(String query) throws ParseException
	{
		Object o = parseQuery(query);
		if (o instanceof UserDefinition)
		{
			return o;
		}
		return Processor.liftProcessor(o);
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
			throw new ParseException(e);
		}
		if (node != null)
		{
			Object o = parseStatement(node);
			return o;
		}
		else
		{
			throw new ParseException("Error: the BNF parser returned null on input " + query);
		}
		//return null;
	}

	public Object parseLanguage(String property, String start_symbol) throws ParseException
	{
		m_parser.setStartRule(start_symbol);
		return parseQuery(property);
	}

	protected Object parseStatement(ParseNode root) throws ParseException
	{
		reset();
		root.postfixAccept(this);
		if (!m_lastExceptions.isEmpty())
		{
			// An exception occurred when traversing the parse tree
			for (Exception e : m_lastExceptions)
			{
				throw new PipingParseException(e);
			}
		}
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

	public static class ParseException extends Exception
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		public ParseException(String message)
		{
			super(message);
		}
		
		public ParseException(Throwable t)
		{
			super(t);
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

	/**
	 * Retrieves the static method of a given class
	 * @param type The class
	 * @param methodName The method name to look for
	 * @param params Any parameters this method may have
	 * @return The method, or null if no method was found
	 */
	static public Method getStaticMethod(Class<?> type, String methodName, Class<?>... params)
	{
		try
		{
			Method method = type.getDeclaredMethod(methodName, params);
			if ((method.getModifiers() & Modifier.STATIC) != 0)
			{
				return method;
			}
		}
		catch (NoSuchMethodException e)
		{
		}
		return null;
	}

	/**
	 * Retrieves a method of a given object
	 * @param o The object
	 * @param methodName The method name to look for
	 * @param params Any parameters this method may have
	 * @return The method, or <code>null</code> if no method was found
	 */
	static public Method getMethod(Object o, String methodName, Class<?>... params)
	{
		try
		{
			Method method = o.getClass().getDeclaredMethod(methodName, params);
			return method;
		}
		catch (NoSuchMethodException e)
		{
		}
		return null;
	}

	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		for (String key : m_processorDefinitions.keySet())
		{
			GroupProcessor pd = m_processorDefinitions.get(key);
			out.append(pd).append("\n");
		}
		for (String key : m_symbolDefinitions.keySet())
		{
			Object pd = m_symbolDefinitions.get(key);
			out.append(pd).append("\n");
		}
		return out.toString();
	}

	/**
	 * Sets the interpreter into "debug mode". This should normally only
	 * be useful for debugging and testing purposes.
	 * @param b Set to true to get debug info
	 */
	@SuppressWarnings("squid:S106")
	public void setDebugMode(boolean b)
	{
		m_parser.setDebugMode(b, System.err);
	}

	/**
	 * Sets the interpreter into "debug mode". This should normally only
	 * be useful for debugging and testing purposes.
	 * @param b Set to true to get debug info
	 * @param out The print stream to send debug info (defaults
	 *   to <code>System.err</code>)
	 */
	public void setDebugMode(boolean b, PrintStream out)
	{
		m_parser.setDebugMode(b, out);
	}

	/**
	 * Exception thrown when building the chain of processors from
	 * the parse tree
	 */
	public static class PipingParseException extends ParseException
	{
		protected final Exception m_exception;

		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		PipingParseException(Exception e)
		{
			super(e);
			m_exception = e;
		}

		@Override
		public String getMessage()
		{
			return m_exception.getMessage();
		}

		@Override
		public Throwable getCause()
		{
			return m_exception;
		}

	}

	void addRule(int i, BnfRule rule)
	{
		m_parser.addRule(i, rule);
	}

	/**
	 * Checks if an object is a specific string
	 * @param o The object
	 * @param symbol The string
	 * @return True if the object is the string
	 */
	public static boolean isSymbol(Object o, String symbol)
	{
		return o instanceof String && ((String) o).toString().compareTo(symbol) == 0;
	}
}
