/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * Duplicates an input event into two or more output events
 * @author sylvain
 *
 */
public final class SmartFork extends Processor
{
	private List<Object> m_inputEvents;
	
	protected int[] m_cursors;
	
	/**
	 * After how many calls to <code>pull()</code> or <code>push()</code>
	 * do we call the cleanup of the input queue
	 */
	protected static final int s_cleanInterval = 10;
	
	/**
	 * How many calls to <code>pull()</code> or <code>push()</code>
	 * since last cleanup of the input queue
	 */
	protected int m_timeSinceLastClean;
	
	public SmartFork(int out_arity)
	{
		super(1, out_arity);
		m_inputEvents = new ArrayList<Object>();
		m_cursors = new int[out_arity];
		m_timeSinceLastClean = 0;
	}
	
	/**
	 * Create a fork by extending the arity of another fork
	 * @param out_arity The output arity of the fork
	 * @param reference The fork to copy from
	 */
	public SmartFork(int out_arity, SmartFork reference)
	{
		this(out_arity);
		for (int i = 0; i < reference.m_inputPullables.length; i++)
		{
			m_inputPullables[i] = reference.m_inputPullables[i];
		}
		for (int i = 0; i < reference.m_outputPushables.length; i++)
		{
			m_outputPushables[i] = reference.m_outputPushables[i];
		}
	}

	@Override
	public void reset()
	{
		m_inputEvents.clear();
		for (int i = 0; i < m_cursors.length; i++)
		{
			m_cursors[i] = 0;
		}
		m_timeSinceLastClean = 0;
	}

	@Override
	public Pushable getPushableInput(int index)
	{
		// Ignore index, as a fork always has input arity 1
		return new QueuePushable();
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		return new QueuePullable(index);
	}
	
	protected class QueuePushable implements Pushable
	{
		public QueuePushable()
		{
			super();
		}

		@Override
		public Pushable push(Object o)
		{
			// Just push the event directly to the output pushables
			for (int i = 0; i < m_outputPushables.length; i++)
			{
				m_outputPushables[i].push(o);
			}
			incrementClean();
			return this;
		}
	}
	
	protected void incrementClean()
	{
		m_timeSinceLastClean = (m_timeSinceLastClean + 1) % s_cleanInterval;
		if (m_timeSinceLastClean == 0)
		{
			cleanQueue();
		}
	}
	
	protected class QueuePullable implements Pullable
	{
		protected int m_queueIndex;
		
		public QueuePullable(int index)
		{
			super();
			m_queueIndex = index;
		}

		@Override
		public Object pull()
		{
			Object out = null;
			if (m_cursors[m_queueIndex] >= m_inputEvents.size())
			{
				Object o = m_inputPullables[0].pull();
				if (o != null)
				{
					m_inputEvents.add(o);
				}
			}
			if (m_cursors[m_queueIndex] < m_inputEvents.size())
			{
				out = m_inputEvents.get(m_cursors[m_queueIndex]);
				m_cursors[m_queueIndex]++;
			}
			incrementClean();
			return out;
		}

		@Override
		public Object pullHard()
		{
			Object out = null;
			if (m_cursors[m_queueIndex] >= m_inputEvents.size())
			{
				Object o = m_inputPullables[0].pullHard();
				m_inputEvents.add(o);
			}
			if (m_cursors[m_queueIndex] < m_inputEvents.size())
			{
				out = m_inputEvents.get(m_cursors[m_queueIndex]);
				m_cursors[m_queueIndex]++;
			}
			incrementClean();
			return out;
		}

		@Override
		public NextStatus hasNext()
		{
			if (m_cursors[m_queueIndex] < m_inputEvents.size())
			{
				return NextStatus.YES;
			}
			return m_inputPullables[0].hasNext();
		}

		@Override
		public NextStatus hasNextHard()
		{
			if (m_cursors[m_queueIndex] < m_inputEvents.size())
			{
				return NextStatus.YES;
			}
			return m_inputPullables[0].hasNextHard();
		}		
	}
	
	/**
	 * Cleans the input list, and removes all events at the beginning that
	 * have been consumed by all outputs
	 */
	protected void cleanQueue()
	{
		int i = 0;
		int to_shift = 0;
		Iterator<Object> it = m_inputEvents.iterator();
		while (it.hasNext())
		{
			boolean all_consumed = true;
			for (int j = 0; j < m_cursors.length; j++)
			{
				if (m_cursors[j] <= i)
				{
					// This event was not consumed yet by output j: stop cleaning
					all_consumed = false;
					break;
				}
			}
			if (all_consumed)
			{
				// All queues consumed this event: remove it...
				it.remove();
				// ...and remember to shift the queue indices by one more position
				to_shift++;				
			}
			else
			{
				// Stop cleaning
				break;
			}
			i++;
		}
		// Shift queue indices by the amount of events we removed
		for (int j = 0; j < m_cursors.length; j++)
		{
			m_cursors[j] -= to_shift;
		}
	}
	
	/**
	 * Creates a copy of the current fork with a greater arity
	 * @param out_arity The desired arity for the output fork
	 */
	public void extendOutputArity(int out_arity)
	{
		m_outputArity = out_arity;
		m_cursors = new int[out_arity];
		Pushable[] out_pushables = new Pushable[out_arity];
		for (int i = 0; i < m_outputPushables.length; i++)
		{
			out_pushables[i] = m_outputPushables[i];
		}
		m_outputPushables = out_pushables;
	}
}
