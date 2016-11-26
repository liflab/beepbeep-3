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

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.concurrency.ThreadManager.ManagedThread;
import ca.uqac.lif.cep.tmf.QueueSource;

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
	boolean m_isPulled;
	
	/**
	 * The processor this pipeline will call
	 */
	protected Processor m_processor;
	
	/**
	 * The inputs given to this processor. This consists of a single
	 * front; moreover, currently the pipeline only supports unary
	 * processors, so this array should always be of size 1.
	 */
	Object[] m_inputs;
	
	/**
	 * The output events produced by the processor
	 */
	Queue<Object> m_outQueue;

	/**
	 * The thread in which the pipeline thread is running, if any
	 */
	protected ManagedThread m_managedThread;

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
	 * Pops an event from the pipeline's output queue. This method
	 * does not check that the queue contains an event.
	 * @see #hasEvent()
	 * @return The event
	 */
	synchronized public Object popEvent()
	{
		return m_outQueue.remove();
	}

	/**
	 * Checks that the pipeline's output queue contains at least one event
	 * @return true if the queue is not empty
	 */
	synchronized public boolean hasEvent()
	{
		return !m_outQueue.isEmpty();
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
	synchronized public boolean canDelete()
	{
		return m_outQueue.isEmpty() && (m_managedThread == null || !m_managedThread.isAlive());
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
				synchronized (m_outQueue)
				{
					m_outQueue.add(o);
				}
			}
		} 
		catch (ConnectorException e)
		{
			// Do nothing
		}
	}
}