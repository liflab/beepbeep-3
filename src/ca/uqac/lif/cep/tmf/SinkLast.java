/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2023 Sylvain Hallé

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

import java.util.Queue;

import ca.uqac.lif.cep.ProcessorException;

/**
 * Sink that remembers only the last event sent to it. This event can be queried
 * with {@link #getLast()}.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class SinkLast extends Sink
{
	/**
	 * The last event (or array of events) received
	 */
	protected Object[] m_last = null;

	/**
	 * The number of events received so far
	 */
	protected int m_eventCounter = 0;

	/**
	 * A flag that remembers if the end of trace has been seen.
	 */
	protected boolean m_seenEndOfTrace;

	/**
	 * Creates a new sink last processor
	 */
	public SinkLast()
	{
		this(1);
	}

	/**
	 * Creates a new sink last processor of given input arity
	 * @param in_arity The input arity
	 */
	public SinkLast(int in_arity)
	{
		super(in_arity);
		m_last = null;
		m_eventCounter = 0;
		m_seenEndOfTrace = false;
	}

	/**
	 * Queries if the processor has seen the end of the input trace.
	 * @return {@code true} if the end of trace signal has been received,
	 * {@code false} otherwise
	 * @since 0.11
	 */
	/*@ pure @*/ public boolean seenEndOfTrace()
	{
		return m_seenEndOfTrace;
	}

	@Override
	protected boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException
	{
		super.onEndOfTrace(outputs);
		m_seenEndOfTrace = true;
		return false;
	}

	@Override
	public void reset()
	{
		super.reset();
		m_last = null;
		m_eventCounter = 0;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		m_last = inputs;
		return true;
	}

	/**
	 * Gets the last event front received by this sink.
	 * @return The last event front, or {@code null} if no front has been
	 * received yet
	 */
	/*@ null @*/ public Object[] getLast()
	{
		return m_last;
	}

	@Override
	public SinkLast duplicate(boolean with_state)
	{
		SinkLast s = new SinkLast(getInputArity());
		if (with_state)
		{
			s.m_seenEndOfTrace = m_seenEndOfTrace;
			if (m_last != null)
			{
				for (int i = 0; i < m_last.length; i++)
				{
					s.m_last[i] = m_last[i];
				}
			}
		}
		return s;
	}

	/**
	 * @since 0.10.2
	 */
	@Override
	public Object printState()
	{
		return getInputArity();
	}

	/**
	 * @since 0.10.2
	 */
	@Override
	public SinkLast readState(Object o)
	{
		return new SinkLast(((Number) o).intValue());
	}
}
