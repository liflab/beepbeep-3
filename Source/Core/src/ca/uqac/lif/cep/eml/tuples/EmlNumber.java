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

public class EmlNumber extends EmlConstant
{
	protected Number m_number;
	
	public EmlNumber()
	{
		super();
	}
	
	public EmlNumber(Number n)
	{
		this();
		m_number = n;
	}

	public Number numberValue()
	{
		return m_number.doubleValue();
	}
	
	public int intValue()
	{
		return m_number.intValue();
	}

	@Override
	public void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		stack.push(new EmlNumber((Number) o));
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
