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
package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

public class AttributeDefinitionAs extends AttributeDefinition
{
	protected String m_aliasName;
	
	protected AttributeExpression m_expression;
	
	public AttributeDefinitionAs()
	{
		super();
		m_aliasName = "";
		m_expression = null;
	}

	@Override
	public void build(Stack<Object> stack)
	{
		EmlString alias_name = (EmlString) stack.pop();
		stack.pop(); // AS
		m_expression = (AttributeExpression) stack.pop();
		m_aliasName = alias_name.stringValue();
		stack.push(this);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_expression).append(" AS ").append(m_aliasName);
		return out.toString();
	}
}
