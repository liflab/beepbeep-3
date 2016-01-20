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
package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

public class AttributeNamePlain extends AttributeNameQualified
{	
	public AttributeNamePlain(String name)
	{
		super("", name);
	}

	public static void build(Stack<Object> stack)
	{
		String att_name = EmlString.parseString(stack.pop());
		if (att_name.compareToIgnoreCase("true") == 0)
		{
			stack.push(new BooleanExpression(true));
		}
		else if (att_name.compareToIgnoreCase("false") == 0)
		{
			stack.push(new BooleanExpression(false));
		}
		else
		{
			AttributeNamePlain anp = new AttributeNamePlain(att_name);
			stack.push(anp);
		}
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_attributeName);
		return out.toString();
	}
}
