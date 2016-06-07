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
package ca.uqac.lif.cep.numbers;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.SingleProcessor;

public class EmlNumber extends SingleProcessor
{
	protected final Number m_number;

	public EmlNumber(Number n)
	{
		super(0, 1);
		m_number = n;
	}
	
	public int intValue()
	{
		return m_number.intValue();
	}

	public static void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		if (o instanceof Number)
		{
			stack.push(new EmlNumber((Number) o));
		}
		else if (o instanceof GroupProcessor)
		{
			stack.push(o);
		}
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Queue<Object[]> out = new ArrayDeque<Object[]>();
		Object[] element = new EmlNumber[1];
		element[0] = this;
		out.add(element);
		return out;
	}
	
	@Override
	public EmlNumber clone()
	{
		return new EmlNumber(m_number);
	}
}
