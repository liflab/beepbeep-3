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

import java.util.LinkedList;
import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

public class EmlString extends EmlConstant
{
	protected String m_string;
	
	public EmlString()
	{
		super();
	}
	
	public EmlString(String s)
	{
		this();
		m_string = s;
	}

	public String stringValue()
	{
		return m_string;
	}

	@Override
	public void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		stack.push(new EmlString((String) o));
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		Queue<Vector<Object>> out = new LinkedList<Vector<Object>>();
		Vector<Object> element = new Vector<Object>();
		element.addElement(this);
		out.add(element);
		return out;
	}
}
