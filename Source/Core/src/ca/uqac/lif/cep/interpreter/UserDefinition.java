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

import java.util.Stack;

import ca.uqac.lif.bullwinkle.BnfRule;
import ca.uqac.lif.bullwinkle.BnfRule.InvalidRuleException;
import ca.uqac.lif.cep.Buildable;

public class UserDefinition implements Buildable 
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
	 * Whether we read the definition or an instance of the definition
	 */
	protected boolean m_isInstantiated = false;
	
	/**
	 * A counter so that every definition number is unique
	 */
	protected static int s_defNb = 0;  
	
	/**
	 * The object (processor, constant, etc.) this definition ultimately
	 * stands for
	 */
	protected Object m_standsFor;
	
	public UserDefinition()
	{
		super();
	}

	@Override
	public void build(Stack<Object> stack) 
	{
		stack.pop(); // .
		m_definition = ((String) stack.pop()).trim();
		m_symbolName = ((String) stack.pop()).trim();
		stack.pop(); // THE
		stack.pop(); // IS
		m_pattern = ((String) stack.pop()).trim();
		stack.pop(); // ,
		m_symbolDefs = (SymbolDefinitionList) stack.pop();
		stack.pop(); // WHEN
		stack.push(this);
	}
	
	/**
	 * Adds this user definition to the grammar of an existing interpreter
	 * @param interpreter The interpreter
	 */
	public void addToInterpreter(Interpreter interpreter)
	{
		String pattern = createPattern();
		String non_terminal = "<USERDEF" + s_defNb++ + ">";
		try 
		{
			interpreter.addRule(BnfRule.parseRule(non_terminal + " := " + pattern));
		} 
		catch (InvalidRuleException e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		interpreter.addCaseToRule("<" + m_symbolName + ">", non_terminal);
		interpreter.addAssociation(non_terminal, new UserDefinitionInstance(this));
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
		for (String var_name : m_symbolDefs.keySet())
		{
			out = out.replaceAll(var_name, " <" + m_symbolDefs.get(var_name) + "> ");
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
