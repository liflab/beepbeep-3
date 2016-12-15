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

import java.util.Map;
import java.util.Stack;
import java.util.logging.Level;

import ca.uqac.lif.bullwinkle.BnfRule;
import ca.uqac.lif.bullwinkle.BnfRule.InvalidRuleException;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.tmf.SmartFork;
import ca.uqac.lif.cep.util.BeepBeepLogger;

public class UserDefinition
{
	/**
	 * The definition of each variable occurring in the expression
	 */
	protected final SymbolDefinitionList m_symbolDefs;

	/**
	 * The non-terminal symbol of the grammar this definition adds
	 * a new case to
	 */
	protected final String m_symbolName;

	/**
	 * The definition
	 */
	protected final String m_definition;

	/**
	 * The parsing pattern
	 */
	protected final String m_pattern;

	/**
	 * An interpreter to parse the definition
	 */
	protected Interpreter m_interpreter;

	/**
	 * The object (processor, constant, etc.) this definition ultimately
	 * stands for
	 */
	protected Object m_standsFor;

	public UserDefinition(SymbolDefinitionList sdl, String symbol_name, String definition, String pattern)
	{
		super();
		m_definition = definition;
		m_pattern = pattern;
		m_symbolDefs = sdl;
		// Hack; we assume all non-terminals in the grammar are lowercase,
		// and allow a query to refer to them in uppercase
		m_symbolName = symbol_name.toLowerCase();
	}

	void setInterpreter(Interpreter i)
	{
		m_interpreter = i;
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		// We use toString: if the definition is a single number, a number is
		// on the stack rather than a string
		String definition = ((String) stack.pop().toString()).trim();
		String symbolName = ((String) stack.pop()).trim();
		stack.pop(); // THE
		stack.pop(); // IS
		String pattern = ((String) stack.pop()).trim();
		SymbolDefinitionList symbol_defs = null;
		if (!stack.isEmpty())
		{
			Object separator = stack.pop();
			if (separator instanceof String && ((String) separator).compareTo(":") == 0)
			{
				// This is a definition with a context
				symbol_defs = (SymbolDefinitionList) stack.pop();
				stack.pop(); // WHEN
			}
		}
		UserDefinition ud = new UserDefinition(symbol_defs, symbolName, definition, pattern);
		stack.push(ud);
	}

	Object parseDefinition(Map<String,Object> symbol_defs)
	{
		Interpreter inner_int = new Interpreter(m_interpreter);
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
					inner_int.addRule(0, rule);
				}
				catch (InvalidRuleException e)
				{
					BeepBeepLogger.logger.log(Level.SEVERE, "", e);
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
				SmartFork f = inner_int.m_processorForks.get(placeholder);
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
	 * @param i The interpreter to add the definition to
	 */
	public void addToInterpreter(Interpreter i)
	{
		if (m_interpreter == null)
		{
			m_interpreter = i;
		}
		String pattern = createPattern();
		String non_terminal = "<USERDEF" + Interpreter.s_defNb++ + ">";
		try
		{
			m_interpreter.addRule(BnfRule.parseRule(non_terminal + " := " + pattern));
		}
		catch (InvalidRuleException e)
		{
			BeepBeepLogger.logger.log(Level.SEVERE, "", e);
		}
		m_interpreter.addCaseToRule("<" + m_symbolName + ">", non_terminal);
		m_interpreter.addUserDefinedAssociation(non_terminal, new UserDefinitionInstance(this));
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
}
