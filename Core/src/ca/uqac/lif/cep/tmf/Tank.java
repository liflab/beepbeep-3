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
import java.util.Queue;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;

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
public class Tank extends SingleProcessor 
{
	/**
	 * A queue to hold incoming events
	 */
	protected Queue<Object> m_queue;
	
	/**
	 * A lock for accessing the queue in a thread-safe manner
	 */
	protected Lock m_lock;
	
	/**
	 * Creates a new empty tank
	 */
	public Tank()
	{
		super(1, 1);
		m_queue = new ArrayDeque<Object>();
		m_lock = new ReentrantLock();
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) throws ProcessorException 
	{
		m_lock.lock();
		if (!m_queue.isEmpty())
		{
			Object o = m_queue.remove();
			outputs.add(new Object[]{o});
		}
		m_lock.unlock();
		return true;
	}

	@Override
	public Tank clone() 
	{
		return new Tank();
	}
	
	@Override
	public Pushable getPushableInput(int index)
	{
		return new QueuePushable();
	}
	
	protected class QueuePushable implements Pushable
	{
		public QueuePushable()
		{
			super();
		}

		@Override
		public Pushable push(Object o) throws PushableException 
		{
			m_lock.lock();
			m_queue.add(o);
			m_lock.unlock();
			return this;
		}

		@Override
		public Pushable pushFast(Object o) throws PushableException 
		{
			return push(o);
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
		m_lock.lock();
		m_queue.clear();
		m_lock.unlock();
	}
}
