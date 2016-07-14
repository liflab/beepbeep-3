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
package ca.uqac.lif.cep.signal;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.tuples.EmlNumber;

public class Threshold extends SingleProcessor
{
	/**
	 * The threshold to cut values
	 */
	protected final float m_threshold;
	
	public Threshold(float threshold)
	{
		super(1, 1);
		m_threshold = threshold;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		float value = EmlNumber.parseFloat(inputs[0]);
		if (Math.abs(value) > m_threshold)
		{
			return wrapObject(value);
		}
		return wrapObject(0);
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		float t_value = EmlNumber.parseFloat(stack.pop());
		stack.pop(); // THRESHOLD
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		Threshold t = new Threshold(t_value);
		Connector.connect(p, t);
		stack.push(t);		
	}
	
	@Override
	public Threshold clone()
	{
		return new Threshold(m_threshold);
	}

}
