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

import java.util.Iterator;

import ca.uqac.lif.cep.NextStatus;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;

/**
 * Accumulates pushed events into a queue until they are pulled.
 * The Tank is a way to bridge an upstream part of a
 * processor chain that works in <em>push</em> mode, to a downstream part
 * that operates in <em>pull</em> mode.
 * <p>
 * Graphically, this processor is represented as:
 * <p>
 * <a href="{@docRoot}/doc-files/tmf/Tank.png"><img
 *   src="{@docRoot}/doc-files/tmf/Tank.png"
 *   alt="Processor graph"></a>
 * <p>
 * The opposite of the tank is the {@link ca.uqac.lif.tmf.Pump Pump}.
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class Tank extends Processor 
{	
	/**
	 * A pushable
	 */
	protected QueuePushable m_pushable = null;
	
	/**
	 * A pullable
	 */
	protected QueuePullable m_pullable = null;

	/**
	 * Creates a new empty tank
	 */
	public Tank()
	{
		super(1, 1);
	}

	@Override
	public Tank duplicate() 
	{
		return new Tank();
	}

	@Override
	public Pushable getPushableInput(int index)
	{
		if (m_pushable == null)
		{
			m_pushable = new QueuePushable(false);
		}
		return m_pushable;
	}
	
	@Override
	public Pullable getPullableOutput(int index)
	{
		if (m_pullable == null)
		{
			m_pullable = new QueuePullable();
		}
		return m_pullable;
	}
	
	protected class QueuePullable implements Pullable
	{
		@Override
		public Iterator<Object> iterator() 
		{
			return this;
		}
		
		@Override
		public void remove()
		{
			// Nothing to do
		}

		@Override
		public Object pullSoft()
		{
			synchronized (m_inputQueues[0])
			{
				return m_inputQueues[0].poll();
			}
		}

		@Override
		public Object pull() 
		{
			synchronized (m_inputQueues[0])
			{
				return m_inputQueues[0].poll();
			}
		}

		@Override
		@SuppressWarnings("squid:S2272")
		public Object next()
		{
			return pull();
		}

		@Override
		public NextStatus hasNextSoft()
		{
			synchronized (m_inputQueues[0])
			{
				if (m_inputQueues[0].isEmpty())
				{
					return NextStatus.MAYBE;
				}
				return NextStatus.YES;
			}
		}

		@Override
		public boolean hasNext() 
		{
			synchronized (m_inputQueues)
			{
				return !m_inputQueues[0].isEmpty();
			}
		}

		@Override
		public Processor getProcessor() 
		{
			return Tank.this;
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
		
	}

	protected class QueuePushable implements Pushable
	{
		private final boolean m_singleObject;

		public QueuePushable(boolean single_object)
		{
			super();
			m_singleObject = single_object;
		}

		@Override
		public Pushable push(Object o) 
		{
			synchronized (m_inputQueues[0])
			{
				if (m_singleObject)
				{
					m_inputQueues[0].clear();
				}
				m_inputQueues[0].add(o);
			}
			return this;
		}

		@Override
		public Pushable pushFast(Object o) 
		{
			return push(o);
		}
		
		@Override
		public void notifyEndOfTrace() throws PushableException {
			// TODO: to be verified
			m_outputPushables[0].notifyEndOfTrace();
		}

		@Override
		public Processor getProcessor() 
		{
			return Tank.this;
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

	@Override
	public void reset()
	{
		synchronized (m_inputQueues[0])
		{
			m_inputQueues[0].clear();
		}
	}
}
