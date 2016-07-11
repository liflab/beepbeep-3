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
 * Boolean implementation of the LTL <b>F</b> processor
 * @author Sylvain Hallé
 */
public class Eventually extends SingleProcessor 
{
	protected int m_notTrueCount = 0;
	
	public Eventually()
	{
		super(1, 1);
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_notTrueCount = 0;
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException 
	{
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // F
		Eventually op = new Eventually();
		Connector.connect(p, op);
		stack.push(op);
	}
	
	@Override
	public Eventually clone()
	{
		return new Eventually();
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs) 
	{
		Queue<Object[]> out = newQueue();
		Value v = Troolean.trooleanValue(inputs[0]);
		if (v == Value.TRUE)
		{
			for (int i = 0; i < m_notTrueCount; i++)
			{
				Object[] e = new Object[1];
				e[0] = Value.TRUE;
				out.add(e);
			}
			m_notTrueCount = 0;
		}
		else
		{
			m_notTrueCount++;
		}
		return out;
	}
}
