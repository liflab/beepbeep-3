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
import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

/**
 * Troolean version of the LTL <b>U</b> operator
 * @author Sylvain Hallé
 */
public class UpTo extends BinaryProcessor 
{
	protected CumulativeFunction<Value> m_left;

	protected CumulativeFunction<Value> m_right;

	protected Value m_currentValue;

	public UpTo()
	{
		super();
		m_left = new Always();
		m_right = new Sometime();
		m_currentValue = Value.INCONCLUSIVE;
	}

	@Override
	public void reset()
	{
		super.reset();
		m_left.reset();
		m_right.reset();
		m_currentValue = Value.INCONCLUSIVE;
	}

	@Override
	protected Object compute(Value left, Value right)
	{
		if (m_currentValue == Value.INCONCLUSIVE)
		{
			Value v_left = m_left.evaluate(left);
			Value v_right = m_right.evaluate(right);
			if (v_right == Value.TRUE)
			{
				m_currentValue = Value.TRUE;
			}
			else if (v_left == Value.FALSE)
			{
				m_currentValue = Value.FALSE;
			}
		}
		return m_currentValue;
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
