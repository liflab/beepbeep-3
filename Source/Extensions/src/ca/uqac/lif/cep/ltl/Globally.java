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
 * Boolean implementation of the LTL <b>G</b> processor
 * @author Sylvain Hallé
 */
public class Globally extends SingleProcessor 
{
	protected int m_notFalseCount = 0;
	
	public Globally()
	{
		super(1, 1);
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_notFalseCount = 0;
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException, ConnectorException 
	{
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // G
		Globally op = new Globally();
		Connector.connect(p, op);
		stack.push(op);
	}
	
	@Override
	public Globally clone()
	{
		return new Globally();
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs) 
	{
		Queue<Object[]> out = newQueue();
		Value v = Troolean.trooleanValue(inputs[0]);
		if (v == Value.FALSE)
		{
			for (int i = 0; i < m_notFalseCount; i++)
			{
				Object[] e = new Object[1];
				e[0] = Value.FALSE;
				out.add(e);
			}
			m_notFalseCount = 0;
		}
		else
		{
			m_notFalseCount++;
		}
		return out;
	}
}
