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

import java.util.Queue;
import java.util.ArrayDeque;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.numbers.EmlNumber;

/**
 * After returning an input event, discards all others for the next
 * <i>n</i> seconds. This processor therefore acts as a rate limiter.
 * <p>
 * Note that this processor uses <code>System.nanoTime()</code> as its
 * clock.
 * However, a mode can be specified in order to output the last input
 * event of the trace if it has not been output already.
 * 
 * @author Sylvain Hallé
 */
public class TimeDecimate extends SingleProcessor
{
	/**
	 * Interval of time
	 */
	protected final long m_interval;

	/**
	 * The system time when the last event was output
	 */
	protected long m_timeLastSent;

	/**
	 * Indicates if the last input event should be output if does not correspond to the rate
	 */
	protected boolean m_shouldOutputLastInputsAnyway;

	/**
	 *
	 */
	protected Object[] m_lastInputs;

	/**
	 * Instantiates a time decimator
	 * @param interval The interval (in nanoseconds) during which
	 *   events should be discarded after an output event is produced
	 */
	public TimeDecimate(long interval, boolean shouldOutputLastInputsAnyway)
	{
		super(1, 1);
		m_interval = interval;
		m_shouldOutputLastInputsAnyway = shouldOutputLastInputsAnyway;
		m_timeLastSent = -1;
		m_lastInputs = null;
	}

	public TimeDecimate(long interval) {
		this(interval, false);
	}

	@Override
	public void reset()
	{
		super.reset();
		m_timeLastSent = -1;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		Object[] out = null;
		if (m_timeLastSent < 0)
		{
			out = inputs;
			m_timeLastSent = System.nanoTime();
		}
		else
		{
			long current_time = System.nanoTime();
			long time_dif = current_time - m_timeLastSent;
			if (time_dif >= m_interval)
			{
				out = inputs;
				m_timeLastSent = current_time;
				m_lastInputs = null;
			}
			else if(m_shouldOutputLastInputsAnyway)
			{
				m_lastInputs = inputs;
			}
		}
		if (out != null)
		{
			outputs.add(out);
			return true;
		}
		return true;
	}

	@Override
	protected boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException
	{
		if(!m_shouldOutputLastInputsAnyway || m_lastInputs == null)
			return super.onEndOfTrace(outputs);

		outputs.add(m_lastInputs);
		m_lastInputs = null;

		return true;
	}

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		Processor p = (Processor) stack.pop();
		EmlNumber interval = (EmlNumber) stack.pop();
		TimeDecimate out = new TimeDecimate(interval.intValue());
		Connector.connect(p, out);
		stack.push(out);
	}

	@Override
	public TimeDecimate clone()
	{
		return new TimeDecimate(m_interval);
	}
}
