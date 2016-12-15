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
package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.numbers.EmlNumber;

/**
 * Discards the first <i>n</i> events of the input, and outputs
 * the remaining ones.
 * 
 * @author Sylvain Hallé
 *
 */
public class Trim extends SingleProcessor
{
	/**
	 * How many events to ignore at the beginning of the trace
	 */
	protected final int m_delay;

	/**
	 * The number of events received so far
	 */
	protected int m_eventsReceived;

	/**
	 * Creates a new delay processor.
	 * @param delay The number of events from the input trace to discard
	 */
	public Trim(int delay)
	{
		super(1, 1);
		m_delay = delay;
	}

	@Override
	public void reset()
	{
		super.reset();
		m_eventsReceived = 0;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		m_eventsReceived++;
		if (m_eventsReceived > m_delay)
		{
			return wrapVector(inputs);
		}
		return new ArrayDeque<Object[]>();
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		//stack.pop(); // )
		Processor p = (Processor) stack.pop();
		//stack.pop(); // (
		stack.pop(); // OF
		EmlNumber delay = (EmlNumber) stack.pop();
		stack.pop(); // TRIM
		Trim out = new Trim(delay.intValue());
		Connector.connect(p, out);
		stack.push(out);
	}

	@Override
	public Trim clone()
	{
		return new Trim(m_delay);
	}
}
