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

import java.util.Arrays;
import java.util.Iterator;

import ca.uqac.lif.cep.NextStatus;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;

/**
 * Merges the contents of multiple traces into a single trace.
 * The multiplexer ("muxer") is an <i>n</i>:1 processor. However, contrarily
 * to other <i>n</i>:1 processors, the multiplexer does not wait until all
 * its <i>n</i> inputs produced an event before doing something. It directly
 * sends to its (single) output whatever events come from any of its inputs.
 * <p>
 * The muxer provides the following guarantees:
 * <ul>
 * <li>All input events are sent to the output</li>
 * <li>All input events received at step <i>k</i> will be output
 * before any event received at step <i>k</i>+1</li>
 * <li>There is no guarantee as to the output ordering of events received
 * at the same step</li>
 * </ul>
 * <p>
 * In other words, the muxer provides a way to merge <i>n</i> input traces
 * into a single one, preserving the relative ordering of events coming
 * from the same input trace.
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class Multiplex extends Processor
{
	/** 
	 * Array containing for each PushableInput of the processor 
	 * if it has been notified of the end of trace or not.
	 * Used to determine if the Multiplexer should notify its 
	 * PushableOutput of the end of trace or not
	 */
	private boolean[] m_havePushableInputsReachedEnd;

	/**
	 * Instantiates a multiplexer
	 * @param in_arity The input arity of the multiplexer. This is the
	 *   number of input traces that should be merged together in the output
	 */
	public Multiplex(int in_arity)
	{
		super(in_arity, 1);
		m_havePushableInputsReachedEnd = new boolean[in_arity];
		Arrays.fill(m_havePushableInputsReachedEnd, false);
	}

	@Override
	public final Pushable getPushableInput(int index)
	{
		// The muxer will directly push to its output whatever
		// comes from any of its inputs, so we don't care about the index
		return new MuxPushable(index);
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		// We ignore index, as it is supposed to be 0 (the muxer is of arity 1)
		return new MuxPullable();
	}

	@Override
	public Multiplex duplicate()
	{
		return new Multiplex(getInputArity());
	}

	protected final class MuxPullable implements Pullable
	{
		public MuxPullable()
		{
			super();
		}

		@Override
		public void remove()
		{
			// Cannot remove an event on a pullable
			throw new UnsupportedOperationException();
		}

		@Override
		public void start()
		{
			// Do nothing
		}

		@Override
		public void stop()
		{
			// Do nothing
		}

		@Override
		public Object pullSoft()
		{
			if (!m_outputQueues[0].isEmpty())
			{
				return m_outputQueues[0].remove();
			}
			for (Pullable p : m_inputPullables)
			{
				Object o = p.pullSoft();
				if (o != null)
				{
					m_outputQueues[0].add(o);
				}
			}
			if (!m_outputQueues[0].isEmpty())
			{
				return m_outputQueues[0].remove();
			}
			return null;
		}

		@Override
		public Object pull()
		{
			if (!m_outputQueues[0].isEmpty())
			{
				return m_outputQueues[0].remove();
			}
			for (Pullable p : m_inputPullables)
			{
				Object o = p.pull();
				if (o != null)
				{
					m_outputQueues[0].add(o);
				}
			}
			// The next instruction may throw a NoSuchElementException.
			// That's OK
			return m_outputQueues[0].remove();
		}

		@Override
		@SuppressWarnings("squid:S2272") // since() pull throws the exception
		public final Object next()
		{
			return pull();
		}

		@Override
		public NextStatus hasNextSoft()
		{
			if (!m_outputQueues[0].isEmpty())
			{
				return NextStatus.YES;
			}
			boolean all_no = true;
			NextStatus out = NextStatus.MAYBE;
			for (Pullable p : m_inputPullables)
			{
				NextStatus ns = p.hasNextSoft();
				if (ns != NextStatus.NO)
				{
					all_no = false;
				}
				if (ns == NextStatus.YES)
				{
					// We don't do a "break" here.
					// We must go through ALL pullables, even if we encounter one
					// that says yes. Otherwise, we might end up pulling events from
					// the same pullable all the time.
					out = NextStatus.YES;
				}
			}
			if (all_no)
			{
				return NextStatus.NO;
			}
			return out;
		}

		@Override
		public boolean hasNext()
		{
			if (!m_outputQueues[0].isEmpty())
			{
				return true;
			}
			boolean all_no = true;
			NextStatus out = NextStatus.MAYBE;
			for (int i = 0; i < Processor.MAX_PULL_RETRIES; i++)
			{
				for (Pullable p : m_inputPullables)
				{
					boolean ns = p.hasNext();
					if (ns)
					{
						all_no = false;
						// We don't do a "break" here.
						// We must go through ALL pullables, even if we encounter one
						// that says yes. Otherwise, we might end up pulling events from
						// the same pullable all the time.
						out = NextStatus.YES;
					}
				}
				if (all_no)
				{
					return false;
				}
				if (out == NextStatus.YES)
				{
					return true;
				}
			}
			// We went through the maximum number of retries without getting
			// anything; declare defeat and return NO
			return false;
		}

		@Override
		public Processor getProcessor()
		{
			return Multiplex.this;
		}

		@Override
		public int getPosition()
		{
			return 0;
		}

		@Override
		public Iterator<Object> iterator()
		{
			return this;
		}

		@Override
		public void dispose()
		{
			// Do nothing
		}
	}

	protected final class MuxPushable implements Pushable
	{
		/**
		 * The index this pushable is linked to
		 */
		private int m_index;

		public MuxPushable(int index)
		{
			super();
			m_index = index;
		}

		@Override
		public Pushable push(Object o)
		{
			m_outputPushables[0].push(o);
			m_outputPushables[0].waitFor();
			return this;
		}

		@Override
		public Pushable pushFast(Object o)
		{
			m_outputPushables[0].pushFast(o);
			return this;
		}

		@Override
		public void notifyEndOfTrace() throws PushableException {
			m_havePushableInputsReachedEnd[m_index] = true;
						
			for(boolean hasReachedEnd : m_havePushableInputsReachedEnd)
			{
				if(!hasReachedEnd)
					return;
			}
			
			m_outputPushables[0].notifyEndOfTrace();
		}
		
		@Override
		public Processor getProcessor()
		{
			return Multiplex.this;
		}

		@Override
		public int getPosition()
		{
			return m_index;
		}

		@Override
		public void waitFor()
		{
			m_outputPushables[0].waitFor();
		}

		@Override
		public void dispose()
		{
			m_outputPushables[0].dispose();
		}
	}
}
