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
package ca.uqac.lif.cep.ltl;

import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class Until extends BinaryProcessor 
{
	protected Value m_left;
	
	protected Value m_right;
	
	public Until()
	{
		super();
		m_left = Value.TRUE;
		m_right = Value.FALSE;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_left = Value.TRUE;
		m_right = Value.FALSE;
	}

	@Override
	protected Object compute(Object left, Object right)
	{
		if (m_right == Value.TRUE)
		{
			return Value.TRUE;
		}
		if (m_left == Value.FALSE)
		{
			return Value.FALSE;
		}
		m_right = Troolean.or(m_right, right);
		m_left = Troolean.and(m_left, left);
		if (m_right == Value.TRUE)
		{
			return Value.TRUE;
		}
		if (m_left == Value.FALSE)
		{
			return Value.FALSE;
		}
		return null;
	}
	
	public static void build(Stack<Object> stack) 
	{
		stack.pop(); // (
		Processor right = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // U
		stack.pop(); // (
		Processor left = (Processor) stack.pop();
		stack.pop(); // )
		Until op = new Until();
		Connector.connect(left, op, 0, 0);
		Connector.connect(right, op, 0, 1);
		stack.push(op);
	}

	@Override
	public Until clone()
	{
		return new Until();
	}
}
