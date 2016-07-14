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
package ca.uqac.lif.cep.tuples;

import java.util.ArrayDeque;
import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;

public class AttributeList extends ArrayDeque<AttributeDefinition>
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;
	
	public AttributeList()
	{
		super();
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException
	{
		Object top = stack.peek();
		AttributeList new_al = new AttributeList();
		if (top instanceof AttributeList)
		{
			AttributeList al = (AttributeList) stack.pop();
			if (!stack.isEmpty())
			{
				stack.pop(); // ,
				AttributeDefinition def = (AttributeDefinition) stack.pop();
				new_al.add(def);
			}
			new_al.addAll(al);
		}
		else
		{
			AttributeDefinition def = (AttributeDefinition) stack.pop();
			new_al.add(def);
		}
		stack.push(new_al);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		boolean first = true;
		for (AttributeDefinition def : this)
		{
			if (!first)
			{
				out.append(", ");
			}
			first = false;
			out.append(def);
		}
		return out.toString();
	}
}
