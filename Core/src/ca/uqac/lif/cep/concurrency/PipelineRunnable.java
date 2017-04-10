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
package ca.uqac.lif.cep.concurrency;

import java.util.LinkedList;
import java.util.Queue;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.logging.Level;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.concurrency.ThreadManager.ManagedThread;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.util.BeepBeepLogger;

/**
 * Computes all the outputs of a
 * processor on a single input event. The {@link #run()} method of
 * this object repeatedly pulls events from the processor passed to
 * its constructor until its {@link Pullable#hasNext() hasNext()} method
 * returns false. As they are pulled, these events are put in an output
 * queue; the state of that queue can be queried with {@link #hasEvent()},
 * and the resulting events can be retrieved one by one with
 * {@link #popEvent()}.
 * <p>
 * The pipeline runnable can be run within a ManagedThread. If this is
 * the case, when the pipeline has finished querying events, it will
 * call the {@link ManagedThread#dispose() dispose()} method of its
 * thread to signal it can be cleaned up.
 */
class PipelineRunnable implements Runnable
{
	/**
	 * Whether the events given to this pipeline have been retrieved
	 * by a pull (true) or a push (false)
	 */
	private boolean m_isPulled;

	/**
	 * The processor this pipeline will call
	 */
	private Processor m_processor;

	/**
	 * Whether this runnable is done
	 */
	private volatile boolean m_done = false;

	/**
	 * The inputs given to this processor. This consists of a single
	 * front; moreover, currently the pipeline only supports unary
	 * processors, so this array should always be of size 1.
	 */
	private Object[] m_inputs;

	/**
	 * The output events produced by the processor
	 */
	private volatile Queue<Object> m_outQueue;

	/**
	 * A lock to access the queue
	 */
	private Lock m_outQueueLock;

	/**
	 * The thread in which the pipeline thread is running, if any
	 */
	private ManagedThread m_managedThread;

	/**
	 * Creates a new pipeline runnable
	 * @param p The processor this pipeline will call
	 * @param inputs  The inputs given to this processor
	 * @param is_pulled Whether the events given to this pipeline have been
	 * retrieved by a pull (true) or a push (false)
	 */
	PipelineRunnable(Processor p, Object[] inputs, boolean is_pulled)
	{
		super();
		m_processor = p;
		m_inputs = inputs;
		m_outQueue = new LinkedList<Object>();
		m_outQueueLock = new ReentrantLock();
		m_isPulled = is_pulled;
	}

	public void setThread(ManagedThread thread)
	{
		m_managedThread = thread;
	}

	public void dispose()
	{
		// Tell the thread manager that the thread in which
		// we were running is no longer used (if any)
		if (m_managedThread != null)
		{
			m_managedThread.dispose();
		}
	}
	
	/**
	 * Gets the processor instance associated to this pipeline runnable
	 * @return The processor
	 */
	Processor getProcessor()
	{
		return m_processor;
	}

	/**
	 * Pops an event from the pipeline's output queue. This method
	 * does not check that the queue contains an event.
	 * @see #hasEvent()
	 * @return The event
	 */
	public Object popEvent()
	{
		m_outQueueLock.lock();
		Object o = m_outQueue.remove();
		m_outQueueLock.unlock();
		return o;
	}

	/**
	 * Checks that the pipeline's output queue contains at least one event
	 * @return true if the queue is not empty
	 */
	public boolean hasEvent()
	{
		m_outQueueLock.lock();
		boolean b = !m_outQueue.isEmpty();
		m_outQueueLock.unlock();
		return b;
	}

	/**
	 * Determines if this pipeline runnable can be deleted. The pipeline
	 * can be deleted when:
	 * <ul>
	 * <li>The thread in which it runs is no longer alive, or the pipeline
	 *  was not running within a thread; AND</li>
	 * <li>All the output events in the output queue have been removed</li>
	 * </ul>
	 * @return
	 */
	public boolean canDelete()
	{
		m_outQueueLock.lock();
		boolean condition = m_outQueue.isEmpty() && m_done;
		m_outQueueLock.unlock();
		return condition;
	}

	@Override
	public void run()
	{
		QueueSource qs = new QueueSource();
		qs.loop(false);
		qs.addEvent(m_inputs[0]);
		try
		{
			Connector.connect(qs, m_processor);
			Pullable pullable = m_processor.getPullableOutput();
			while (pullable.hasNext())
			{
				Object o = pullable.pull();
				m_outQueueLock.lock();
				m_outQueue.add(o);
				m_outQueueLock.unlock();
			}
		}
		catch (ConnectorException e)
		{
			BeepBeepLogger.logger.log(Level.SEVERE, "", e);
		}
		m_done = true;
		dispose();
	}

	/**
	 * Sets if the events given to this pipeline have been retrieved
	 * by a {@link ca.uqac.lif.cep.Pullable#pull() pull()} or a
	 * {@link ca.uqac.lif.cep.Pushable#push() push()}
	 * @param b Set to <code>true</code> to indicate pull
	 */
	public void setIsPulled(boolean b)
	{
		m_isPulled = b;
	}

	/**
	 * Checks if the events given to this pipeline have been retrieved
	 * by a {@link ca.uqac.lif.cep.Pullable#pull() pull()} or a
	 * {@link ca.uqac.lif.cep.Pushable#push() push()}
	 * @return <code>true</code> to indicate pull, <code>false</code>
	 *   otherwise
	 */
	public boolean getIsPulled()
	{
		return m_isPulled;
	}

	public boolean isDone()
	{
		return m_done;
	}
}