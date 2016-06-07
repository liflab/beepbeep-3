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
package ca.uqac.lif.cep.epl;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * After returning an input event, discards all others for the next
 * <i>n</i> seconds. This processor therefore acts as a rate limiter.
 * <p>
 * Note that this processor uses <code>System.nanoTime()</code> as its
 * clock.
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
	 * Instantiates a time decimator
	 * @param interval The interval (in nanoseconds) during which
	 *   events should be discarded after an output event is produced 
	 */
	public TimeDecimate(long interval)
	{
		super(1, 1);
		m_interval = interval;
		m_timeLastSent = -1;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_timeLastSent = -1;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object[] out = null;
		if (m_timeLastSent < 0)
		{
			out = inputs;
		}
		else
		{
			long current_time = System.nanoTime();
			long time_dif = current_time - m_timeLastSent;
			if (time_dif >= m_interval)
			{
				out = inputs;
			}
		}
		return wrapVector(out);
	}
	
	public static void build(Stack<Object> stack)
	{
		Processor p = (Processor) stack.pop();
		Number interval = (Number) stack.pop();
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
