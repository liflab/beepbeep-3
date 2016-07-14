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
package ca.uqac.lif.cep.ltl;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

/**
 * Boolean implementation of the LTL <b>U</b> processor
 * @author Sylvain Hallé
 */
public class Until extends SingleProcessor 
{
	protected int m_eventCount = 0;
	
	public Until()
	{
		super(2, 1);
		m_eventCount = 0;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_eventCount = 0;
	}

	@Override
	protected Queue<Object[]> compute(Object[] input)
	{
		Value left = Troolean.trooleanValue(input[0]);
		Value right = Troolean.trooleanValue(input[1]);
		Queue<Object[]> out = newQueue();
		m_eventCount++;
		if (right == Value.TRUE)
		{
			for (int i = 0; i < m_eventCount; i++)
			{
				Object[] e = new Object[1];
				e[0] = Value.TRUE;
				out.add(e);
				m_eventCount = 0;
			}
			return out;
		}
		if (left == Value.FALSE)
		{
			for (int i = 0; i < m_eventCount; i++)
			{
				Object[] e = new Object[1];
				e[0] = Value.FALSE;
				out.add(e);
				m_eventCount = 0;
			}
			return out;			
		}
		return null;
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException 
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
