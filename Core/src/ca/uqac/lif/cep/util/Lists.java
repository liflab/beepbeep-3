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
package ca.uqac.lif.cep.util;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * A container object for functions and processors applying to lists.
 * @author Sylvain Hallé
 */
public class Lists
{
	private Lists()
	{
		// Utility class
	}
	
	/**
	 * Accumulates events that are being pushed, and sends them in a burst
	 * into a list at predefined time intervals.
	 * <p>
	 * This processor only works in <strong>push</strong> mode. It is represented
	 * graphically as follows:
	 * <p>
	 * <a href="{@docRoot}/doc-files/ListPacker.png"><img
	 *   src="{@docRoot}/doc-files/ListPacker.png"
	 *   alt="Processor graph"></a>
	 * 
	 * @author Sylvain Hallé
	 */
	public static class Pack extends SingleProcessor 
	{	
		/**
		 * The list of events accumulated since the last output
		 */
		protected List<Object> m_packedEvents;
		
		/**
		 * A lock to access the list of objects
		 */
		protected Lock m_lock;
		
		/**
		 * The interval, in milliseconds, at which events will be pushed to
		 * the output 
		 */
		protected long m_outputInterval;
		
		/**
		 * The timer that will send events at periodic interval
		 */
		protected Timer m_timer;
		
		/**
		 * The thread that will execute the timer
		 */
		protected Thread m_timerThread;
		
		/**
		 * Creates a new list packer.
		 * @param interval The interval, in milliseconds, at which events will
		 *   be pushed to the output
		 */
		public Pack(long interval)
		{
			super(1, 1);
			setInterval(interval);
			m_lock = new ReentrantLock();
			m_packedEvents = new LinkedList<Object>();
		}
		
		/**
		 * Creates a new list packer with a default interval of 1 second. 
		 */
		public Pack()
		{
			this(1000);
		}
		
		/**
		 * Sets the interval at which events are output
		 * @param interval The interval, in milliseconds
		 * @return This processor
		 */
		public Pack setInterval(long interval)
		{
			m_outputInterval = interval;
			return this;
		}
		
		@Override
		public void start()
		{
			m_timer = new Timer();
			m_timerThread = new Thread(m_timer);
			m_timerThread.start();
		}
		
		@Override
		public void stop()
		{
			m_timer.stop();
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
		{
			m_lock.lock();
			m_packedEvents.add(inputs[0]);
			m_lock.unlock();
			return true;
		}
		
		/**
		 * Timer that pushes the contents of <code>m_packedEvents</code> every
		 * <code>m_outputInterval</code> milliseconds.
		 */
		protected class Timer implements Runnable
		{
			protected volatile boolean m_run = true;
			
			public void stop()
			{
				m_run = false;
			}
			
			@Override
			public void run() 
			{
				m_run = true;
				while (m_run)
				{
					try 
					{
						Thread.sleep(m_outputInterval);
					}
					catch (InterruptedException e) 
					{
						// Restore interrupted state
						Thread.currentThread().interrupt();
					}
					Pushable p = getPushableOutput(0);
					m_lock.lock();
					p.push(m_packedEvents);
					m_packedEvents = new LinkedList<Object>();
					m_lock.unlock();				
				}
			}		
		}
		
		@Override
		public Pullable getPullableOutput(int position)
		{
			return new Pullable.PullNotSupported(this, position);
		}

		@Override
		public Pack duplicate() 
		{
			return new Pack();
		}
	}
	/**
	 * Unpacks a list of objects by outputting its contents as separate events.
	 * This processor is represented graphically as follows:
	 * <p>
	 * <a href="{@docRoot}/doc-files/ListUnpacker.png"><img
	 *   src="{@docRoot}/doc-files/ListUnpacker.png"
	 *   alt="Processor graph"></a>
	 * 
	 * @author Sylvain Hallé
	 */
	public static class Unpack extends SingleProcessor 
	{
		/**
		 * Creates a new list unpacker
		 */
		public Unpack()
		{
			super(1, 1);
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
		{
			@SuppressWarnings("unchecked")
			List<Object> list = (List<Object>) inputs[0];
			for (Object o : list)
			{
				outputs.add(new Object[]{o});
			}
			return true;
		}

		@Override
		public Unpack duplicate() 
		{
			return new Unpack();
		}
	}
}
