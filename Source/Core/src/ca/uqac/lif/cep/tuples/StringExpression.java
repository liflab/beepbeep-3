/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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
package ca.uqac.lif.cep.tuples;

import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.util.CacheMap;

public class StringExpression extends ConstantExpression
{
	private final String m_string;
	
	public StringExpression(String s)
	{
		super();
		m_string = s;
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		String s = EmlString.parseString(stack.pop());
		StringExpression s_exp = new StringExpression(s);
		stack.push(s_exp);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_string);
		return out.toString();
	}
	
	@Override
	public Object evaluate(CacheMap<Object> inputs) 
	{
		return m_string;
	}
}
