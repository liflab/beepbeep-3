/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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
import java.util.Iterator;
import java.util.Queue;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;

/**
 * Processor that acts as a barrier between upstream push events
 * and downstream pull events.
 * <ul>
 * <li>Events are <em>pushed</em> to the processor. Each push
 * results in a call to the method {@link #onPush(Object)},
 * which the user must override to do whatever processing is
 * required.</li>
 * <li>Pushing on the processor's input does not push any
 * output events. Rather, output events have to be explicitly
 * <em>pulled</em>; a call to pull results in a call to
 * {@link #onPull(Queue)}, which the user must override to do whatever
 * processing required to produce an output event.</li>
 * </ul>
 * Therefore, the processor blocks upstream events that are pushed
 * to it, and sends output events only on demand, acting
 * like some sort of "faucet".
 *  
 * @author Sylvain Hallé
 */
public abstract class Faucet extends Processor 
{
	/**
	 * Creates a new faucet
	 */
	public Faucet()
	{
		super(1, 1);
	}
	
	/**
	 * Action to be taken when an input event is pushed
	 * @param e The input event
	 */
	public abstract void onPush(Object e);
	
	/**
	 * Action to be taken when an output event is queried
	 * @param queue A queue where events to be produced should
	 * be placed
	 * @return {@code true} if more events could come, {@code false}
	 * if no output events will ever be produced in the future
	 * @throws ProcessorException If something is wrong when processing
	 */
	public abstract boolean onPull(Queue<Object[]> queue) throws ProcessorException;

	@Override
	public Pushable getPushableInput(int index) 
	{
		return new FaucetPushable();
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		return new FaucetPullable();
	}
	
	/**
	 * Pushable object specific to the updater processor
	 */
	public class FaucetPushable implements Pushable
	{
		@Override
		public Pushable push(Object o) throws PushableException 
		{
			onPush(o);
			return this;
		}

		@Override
		public Pushable pushFast(Object o) throws PushableException 
		{
			return push(o);
		}
		
		@Override
		public void notifyEndOfTrace() throws PushableException {
			// TODO Auto-generated method stub
		}

		@Override
		public Processor getProcessor() 
		{
			return Faucet.this;
		}

		@Override
		public int getPosition() 
		{
			return 0;
		}

		@Override
		public void waitFor() 
		{
			// Nothing to do			
		}

		@Override
		public void dispose() 
		{
			// Nothing to do
		}
		
	}
	
	/**
	 * Pullable object specific to the updater processor
	 */
	public class FaucetPullable implements Pullable, Iterator<Object>
	{
		/**
		 * A queue accumulating the events to be output
		 */
		Queue<Object[]> m_eventsToOutput;
		
		public FaucetPullable()
		{
			super();
			m_eventsToOutput = new ArrayDeque<Object[]>();
		}
		
		@Override
		public Iterator<Object> iterator()
		{
			return this;
		}

		@Override
		public Object pullSoft() throws PullableException
		{
			if (m_eventsToOutput.isEmpty())
			{
				try
				{
					onPull(m_eventsToOutput);
				}
				catch (ProcessorException e)
				{
					throw new PullableException(e);
				}
			}
			if (m_eventsToOutput.isEmpty())
			{
				return null;
			}
			return m_eventsToOutput.poll()[0];
		}

		@Override
		public Object pull() throws PullableException
		{
			while (m_eventsToOutput.isEmpty())
			{
				try
				{
					onPull(m_eventsToOutput);
				}
				catch (ProcessorException e)
				{
					throw new PullableException(e);
				}
			}
			return m_eventsToOutput.poll()[0];
		}

		@Override
		public Object next() throws PullableException
		{
			return pull();
		}

		@Override
		public NextStatus hasNextSoft() throws PullableException
		{
			// Check if events are in the queue
			if (!m_eventsToOutput.isEmpty())
			{
				return NextStatus.YES;
			}
			// Otherwise, try to put some into the queue
			boolean more = true;
			try
			{
				more = onPull(m_eventsToOutput);
			}
			catch (ProcessorException e)
			{
				throw new PullableException(e);
			}
			if (!more)
			{
				// The processor tell us no more events will ever come
				return NextStatus.NO;
			}
			if (!m_eventsToOutput.isEmpty())
			{
				// The processor created some new events
				return NextStatus.YES;
			}
			// The processor did not produce output events, but did not
			// say it could not produce some in the future
			return NextStatus.MAYBE;
		}

		@Override
		public boolean hasNext() throws PullableException
		{
			if (!m_eventsToOutput.isEmpty())
			{
				return true;
			}
			while (m_eventsToOutput.isEmpty())
			{
				boolean more = true;
				try
				{
					more = onPull(m_eventsToOutput);
				}
				catch (ProcessorException e)
				{
					throw new PullableException(e);
				}
				if (!more)
				{
					return false;
				}
			}
			return true;
		}

		@Override
		public Processor getProcessor()
		{
			return Faucet.this;
		}

		@Override
		public int getPosition()
		{
			return 0;
		}

		@Override
		public void start()
		{
			// Nothing to do
		}

		@Override
		public void stop()
		{
			// Nothing to do
		}

		@Override
		public void dispose()
		{
			// Nothing to do
		}
		
		@Override
		public void remove()
		{
			// Nothing to do
		}
	}
}
