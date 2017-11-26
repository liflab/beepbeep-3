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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;

/**
 * Duplicates an input event into two or more output traces. Contrarily to
 * the {@link Fork}, the "smart" fork assumes an input arity of 1, and uses
 * that to optimize the internal buffering of input events into the output
 * queues. (Events are kept into a single queue, rather than be copied into
 * <i>n</i> output queues.) For input arity 1, this object is preferred over
 * {@link Fork}, as it otherwise behaves in exactly the same way.
 * 
 * @author Sylvain Hallé
 *
 */
public final class SmartFork extends Processor
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 9020012031973273018L;

	/**
	 * The buffer of input events
	 */
	private List<Object> m_inputEvents;

	/**
	 * A set of cursors, i.e. pointers to the input buffer. For a fork of
	 * output arity <i>n</i>, there are <i>n</i> cursors.
	 */
	private int[] m_cursors;

	/**
	 * After how many calls to <code>pull()</code> or <code>push()</code>
	 * do we call the cleanup of the input queue
	 */
	protected int m_cleanInterval = 1000;

	/**
	 * How many calls to <code>pull()</code> or <code>push()</code>
	 * since last cleanup of the input queue
	 */
	private int m_timeSinceLastClean;

	/**
	 * Instantiates a fork.
	 * @param out_arity The fork's output arity
	 */
	public SmartFork(int out_arity)
	{
		super(1, out_arity);
		synchronized (this)
		{
			m_inputEvents = new ArrayList<Object>();
			m_cursors = new int[out_arity];
			m_timeSinceLastClean = 0;
		}
	}

	/**
	 * Creates a fork by extending the arity of another fork
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
	
	/**
	 * Sets after how many calls to <code>pull()</code> or <code>push()</code>
	 * do we call the cleanup of the input queue
	 * @param num_events The number of calls
	 */
	public void setCleanInterval(int num_events)
	{
		m_cleanInterval = num_events;
	}

	@Override
	public synchronized SmartFork duplicate()
	{
		SmartFork sm = new SmartFork(getOutputArity());
		sm.setContext(getContext());
		return sm;
	}

	@Override
	public synchronized void reset()
	{
		m_inputEvents.clear();
		for (int i = 0; i < m_cursors.length; i++)
		{
			m_cursors[i] = 0;
		}
		m_timeSinceLastClean = 0;
	}

	/**
	 * Directly puts an event in the fork's input queue. Note that
	 * this bypasses the normal flow of events between processors, and
	 * should be used with much caution.
	 * @param o The event to insert
	 */
	public synchronized void putInQueue(Object o)
	{
		m_inputEvents.add(o);
	}

	@Override
	public Pushable getPushableInput(int index)
	{
		// Ignore index, as a fork always has input arity 1
		return new QueuePushable();
	}

	@Override
	public synchronized Pullable getPullableOutput(int index)
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
		public synchronized Pushable push(Object o)
		{
			// Just push the event directly to the output pushables
			for (int i = 0; i < m_outputPushables.length; i++)
			{
				m_outputPushables[i].push(o);
			}
			incrementClean();
			return this;
		}

		@Override
		public synchronized Pushable pushFast(Object o)
		{
			// Just push the event directly to the output pushables
			for (int i = 0; i < m_outputPushables.length; i++)
			{
				m_outputPushables[i].pushFast(o);
			}
			incrementClean();
			return this;
		}

		@Override
		public synchronized Processor getProcessor()
		{
			return SmartFork.this;
		}

		@Override
		public synchronized int getPosition()
		{
			return 0;
		}

		@Override
		public synchronized void waitFor()
		{
			for (int i = 0; i < m_outputPushables.length; i++)
			{
				m_outputPushables[i].waitFor();
			}
		}

		@Override
		public synchronized void dispose()
		{
			// Do nothing
		}
	}

	/**
	 * Increments the clean counter, which is used to decide when to
	 * perform a clean-up of the input buffer
	 */
	private synchronized void incrementClean()
	{
		m_timeSinceLastClean = (m_timeSinceLastClean + 1) % m_cleanInterval;
		if (m_timeSinceLastClean == 0)
		{
			cleanQueue();
		}
	}

	protected class QueuePullable implements Pullable
	{
		private final int m_queueIndex;

		public QueuePullable(int index)
		{
			super();
			m_queueIndex = index;
		}

		@Override
		public void remove()
		{
			// Cannot remove an event on a pullable
			throw new UnsupportedOperationException();
		}

		@Override
		public Object pullSoft()
		{
			Object out = null;
			if (m_inputPullables[0] == null)
			{
				return out;
			}
			if (m_cursors[m_queueIndex] >= m_inputEvents.size())
			{
				Object o = m_inputPullables[0].pullSoft();
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
		public Object pull()
		{
			Object out = null;
			if (m_inputPullables[0] == null)
			{
				return out;
			}
			if (m_cursors[m_queueIndex] >= m_inputEvents.size())
			{
				Object o = m_inputPullables[0].pull();
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
		public final Object next()
		{
			return pull();
		}

		@Override
		public NextStatus hasNextSoft()
		{
			if (m_cursors[m_queueIndex] < m_inputEvents.size())
			{
				return NextStatus.YES;
			}
			return m_inputPullables[0].hasNextSoft();
		}

		@Override
		public boolean hasNext()
		{
			if (m_cursors[m_queueIndex] < m_inputEvents.size())
			{
				return true;
			}
			return m_inputPullables[0].hasNext();
		}

		@Override
		public Processor getProcessor()
		{
			return SmartFork.this;
		}

		@Override
		public int getPosition()
		{
			return m_queueIndex;
		}

		@Override
		public Iterator<Object> iterator()
		{
			return this;
		}

		@Override
		public void start()
		{
			for (Pullable p : m_inputPullables)
			{
				p.start();
			}
		}

		@Override
		public void stop()
		{
			for (Pullable p : m_inputPullables)
			{
				p.stop();
			}
		}

		@Override
		public void dispose()
		{
			// Do nothing
		}
	}

	/**
	 * Cleans the input list, and removes all events at the beginning that
	 * have been consumed by all outputs
	 */
	synchronized protected void cleanQueue()
	{
		int i = 0;
		int to_shift = 0;
		Iterator<Object> it = m_inputEvents.iterator();
		while (it.hasNext())
		{
			it.next(); // Must call next, otherwise can't call remove() later on
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
	public synchronized void extendOutputArity(int out_arity)
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
