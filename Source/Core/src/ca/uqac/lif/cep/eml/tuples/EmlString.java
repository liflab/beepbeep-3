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

public abstract class EmlString extends EmlConstant
{
	public static void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		if (o instanceof String)
		{
			stack.push((String) o);
		}
		else if (o instanceof Number)
		{
			stack.push(o.toString());
		}
	}
	
	public static String parseString(Object o)
	{
		if (o instanceof String)
		{
			return (String) o;
		}
		return o.toString();
	}
}
