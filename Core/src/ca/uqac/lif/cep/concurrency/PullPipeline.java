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

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Queue;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.concurrency.ThreadManager.ManagedThread;

public class PullPipeline extends Processor implements Runnable
{
	/**
	 * A queue of incoming messages
	 */
	private volatile Queue<Object> m_inQueue;

	/**
	 * A matching queue of Booleans; an entry contains the value
	 * true if the event of <code>m_inQueue</code> was pulled from
	 * the input, and false if it was pushed from it
	 */
	private volatile Queue<Boolean> m_isPulled;

	/**
	 * A lock to access the input queue
	 */
	private Lock m_inQueueLock;

	/**
	 * A list of {@link PipelineRunnable}
	 */
	private volatile LinkedList<PipelineRunnable> m_pipelines;

	/**
	 * A lock to access the pipelines
	 */
	private Lock m_pipelinesLock;

	/**
	 * The maximum number of pipelines that can be in the queue. This is to
	 * prevent generating too many output events that are not consumed
	 * downstream.
	 */
	private int m_maxPipelines = 100;

	/**
	 * The pullable the pipeline will read from
	 */
	private Pullable m_inputPullable;

	/**
	 * The pushable the pipeline will push to
	 */
	private Pushable m_outputPushable;

	/**
	 * Semaphore to stop the pipeline
	 */
	private volatile boolean m_run = false;

	/**
	 * The size after which the pipeline temporarily stops polling
	 * for new events
	 */
	private int m_maxQueueSize = 100;

	/**
	 * The thread manager to get instances of threads
	 */
	private ThreadManager m_threadManager;

	/**
	 * The thread in which the pipeline thread is running
	 */
	private ManagedThread m_managedThread;

	/**
	 * Time (in milliseconds) to wait before polling again
	 */
	protected static final long s_sleepIntervalWhenPolling = 0;

	/**
	 * Time (in milliseconds) to wait when the pipeline sees that its
	 * output queue is at maximum capacity
	 */
	protected static final long s_sleepIntervalWhenFullQueue = 5;

	/**
	 * The processor that will be pipelined
	 */
	private Processor m_processor;

	/**
	 * Creates a new pull pipeline around a processor
	 * @param p The processor
	 */
	public PullPipeline(Processor p, ThreadManager manager)
	{
		super(1, 1);
		synchronized (this)
		{
			m_inQueue = new LinkedList<Object>();
			m_inQueueLock = new ReentrantLock();
			m_isPulled = new LinkedList<Boolean>();
			m_pipelines = new LinkedList<PipelineRunnable>();
			m_pipelinesLock = new ReentrantLock();
			m_processor = p;
			if (manager != null)
			{
				m_threadManager = manager;
			}
			else
			{
				if (ThreadManager.defaultManager != null)
				{
					m_threadManager = ThreadManager.defaultManager;
				}
			}
		}
	}

	/**
	 * Creates a new pull pipeline around a processor
	 * @param p The processor
	 */
	public PullPipeline(Processor p)
	{
		this(p, null);
	}

	@Override
	synchronized public void setPullableInput(int index, Pullable p)
	{
		if (index == 0)
		{
			m_inputPullable = p;
		}
	}

	@Override
	synchronized public void setPushableOutput(int index, Pushable p)
	{
		if (index == 0)
		{
			m_outputPushable = p;
		}
	}

	@Override
	synchronized public Pushable getPushableInput(int index)
	{
		return new PipelinePushable();
	}

	@Override
	synchronized public Pullable getPullableOutput(int index)
	{
		return new PipelinePullable();
	}

	@Override
	synchronized public PullPipeline clone()
	{
		PullPipeline p = new PullPipeline(m_processor.clone());
		p.setContext(m_context);
		p.m_threadManager = m_threadManager;
		return p;
	}

	@Override
	public void setContext(Context context)
	{
		if (context == null)
		{
			return;
		}
		if (m_context == null)
		{
			m_context = new Context();
		}
		m_context.putAll(context);
		m_processor.setContext(context);
	}

	@Override
	public void setContext(String key, Object value)
	{
		if (m_context == null)
		{
			m_context = new Context();
		}
		m_context.put(key, value);
		m_processor.setContext(key, value);
	}

	/**
	 * Shifts the index of each entry of the out map by -1. This method
	 * <em>must</em> be called by another method that has the lock on
	 * <code>m_pipelines</code>.
	 */
	protected Object shiftEntries()
	{
		// Entry 0 is guaranteed to be here if this method is called
		PipelineRunnable thread = m_pipelines.get(0);
		Object o = thread.popEvent();
		if (thread.canDelete())
		{
			// This thread is done; we remove it
			thread.dispose();
			m_pipelines.removeFirst();
		}
		return o;
	}

	/**
	 * Output pullable for the PullPipeline
	 */
	public class PipelinePullable implements Pullable
	{
		@Override
		public void remove()
		{
			// Do nothing
		}

		@Override
		public Iterator<Object> iterator()
		{
			return this;
		}

		@Override
		public Object pullSoft()
		{
			Object out = null;
			if (!m_run)
			{
				// Take this opportunity to perform a cleanup on the pipelines
				pollPullableSoft();
				doThreadHousekeeping();
			}
			m_pipelinesLock.lock();
			if (!m_pipelines.isEmpty() && m_pipelines.getFirst().hasEvent())
			{
				out = shiftEntries();
			}
			m_pipelinesLock.unlock();
			return out;
		}

		@Override
		public Object pull()
		{
			Object out = null;
			if (!m_run)
			{
				// Take this opportunity to perform a cleanup on the pipelines
				if (m_pipelines.size() < m_maxPipelines)
				{
					pollPullableHard();
				}
				doThreadHousekeeping();
			}
			m_pipelinesLock.lock();
			if (!m_pipelines.isEmpty() && m_pipelines.getFirst().hasEvent())
			{
				out = shiftEntries();
			}
			m_pipelinesLock.unlock();
			if (out != null)
			{
				return out;
			}
			// Wait until index 0 appears
			while (m_run)
			{
				ThreadManager.sleep(s_sleepIntervalWhenPolling);
				m_pipelinesLock.lock();
				boolean returned = false;
				if (!m_pipelines.isEmpty() && m_pipelines.getFirst().hasEvent())
				{
					out = shiftEntries();
					returned = true;
				}
				m_pipelinesLock.unlock();
				if (returned)
				{
					return out;
				}
			}
			return null;
		}

		@Override
		public Object next()
		{
			return pull();
		}

		@Override
		public NextStatus hasNextSoft()
		{
			if (!m_run)
			{
				// Take this opportunity to perform a cleanup on the pipelines
				pollPullableSoft();
				doThreadHousekeeping();
			}
			m_pipelinesLock.lock();
			NextStatus to_return = NextStatus.MAYBE;
			if (!m_pipelines.isEmpty())
			{
				to_return = NextStatus.YES;
			}
			m_pipelinesLock.unlock();
			return to_return;
		}

		@Override
		public boolean hasNext()
		{
			boolean condition;
			m_pipelinesLock.lock();
			condition = !m_pipelines.isEmpty() && m_pipelines.getFirst().hasEvent();
			m_pipelinesLock.unlock();
			if (condition)
			{
				return true;
			}
			// If we're running in a thread, wait until index 0 appears
			while (m_run)
			{
				ThreadManager.sleep(s_sleepIntervalWhenPolling);
				m_pipelinesLock.lock();
				condition = !m_pipelines.isEmpty() && m_pipelines.getFirst().hasEvent();
				m_pipelinesLock.unlock();
				if (condition)
				{
					return true;
				}
				m_pipelinesLock.lock();
				if (!m_pipelines.isEmpty() && m_pipelines.getFirst().canDelete())
				{
					// This pipeline is done; remove it
					m_pipelines.removeFirst();
				}
				m_pipelinesLock.unlock();
			}
			// If we're not running in a thread, poll the pullable
			if (!m_run)
			{
				while (true)
				{
					if (m_pipelines.size() < m_maxPipelines)
					{
						pollPullableHard();
					}
					doThreadHousekeeping();
					m_pipelinesLock.lock();
					boolean pipes_empty = m_pipelines.isEmpty();
					condition = !pipes_empty && m_pipelines.getFirst().hasEvent();
					m_pipelinesLock.unlock();
					if (condition)
					{
						return true;
					}
					m_pipelinesLock.lock();
					if (!m_pipelines.isEmpty())
					{
						m_pipelines.removeFirst();
					}
					m_pipelinesLock.unlock();
					pollPullableHard();
					doThreadHousekeeping();
					m_pipelinesLock.lock();
					pipes_empty = m_pipelines.isEmpty();
					m_pipelinesLock.unlock();
					if (pipes_empty)
					{
						return false;
					}
					System.out.println("Polling");
				}			
			}
			return false;
		}

		@Override
		public Processor getProcessor()
		{
			return PullPipeline.this;
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
			PullPipeline.this.stop();
		}

		@Override
		public void dispose()
		{
			m_pipelinesLock.lock();
			Iterator<PipelineRunnable> it = m_pipelines.iterator();
			while (it.hasNext())
			{
				PipelineRunnable pr = it.next();
				pr.dispose();
			}
			m_pipelines.clear();
			m_pipelinesLock.unlock();
		}
	}

	public class PipelinePushable implements Pushable
	{
		@Override
		synchronized public Pushable push(Object o)
		{
			m_inQueue.add(o);
			m_isPulled.add(false);
			doThreadHousekeeping();
			return this;
		}

		@Override
		public Processor getProcessor()
		{
			return PullPipeline.this;
		}

		@Override
		public int getPosition()
		{
			return 0;
		}

		@Override
		public Pushable pushFast(Object o)
		{
			return push(o);
		}

		@Override
		public void waitFor()
		{
			return;
		}

		@Override
		public void dispose()
		{
			m_pipelinesLock.lock();
			Iterator<PipelineRunnable> it = m_pipelines.iterator();
			while (it.hasNext())
			{
				PipelineRunnable pr = it.next();
				pr.dispose();
			}
			m_pipelines.clear();
			m_pipelinesLock.unlock();
		}
	}

	@Override
	public void run()
	{
		while (m_run)
		{
			m_pipelinesLock.lock();
			if (m_pipelines.size() < m_maxPipelines)
			{
				pollPullableHard();
			}
			m_pipelinesLock.unlock();
			boolean b = doThreadHousekeeping();
			if (b)
			{
				ThreadManager.sleep(s_sleepIntervalWhenPolling);
			}
			else
			{
				// Wait a bit longer if queue is full
				ThreadManager.sleep(s_sleepIntervalWhenFullQueue);
			}
		}
	}

	private void pollPullableSoft()
	{
		m_inQueueLock.lock();
		if (m_inQueue.size() < m_maxQueueSize)
		{
			Object o = m_inputPullable.pullSoft();
			if (o != null)
			{
				m_inQueue.add(o);
				m_isPulled.add(true);
			}
		}
		m_inQueueLock.unlock();
	}

	private boolean pollPullableHard()
	{
		m_inQueueLock.lock();
		if (m_inQueue.size() < m_maxQueueSize)
		{
			Object o = m_inputPullable.pull();
			if (o != null)
			{
				m_inQueue.add(o);
				m_isPulled.add(true);
				m_inQueueLock.unlock();
				return true;
			}
			else
			{
				m_run = false;
				m_inQueueLock.unlock();
				return false;
			}
		}
		m_inQueueLock.unlock();
		return true;
	}

	@Override
	public void start()
	{
		if (!m_run)
		{
			m_managedThread = m_threadManager.tryNewThread(this);
			if (m_managedThread != null)
			{
				m_run = true;
				m_managedThread.start();
			}
		}
	}

	@Override
	public void stop()
	{
		m_run = false;
		if (m_managedThread != null)
		{
			m_managedThread.dispose();
		}
	}

	private boolean doThreadHousekeeping()
	{
		Object event = null;
		boolean is_pulled = false;
		boolean to_return = true;
		m_inQueueLock.lock();
		if (!m_inQueue.isEmpty())
		{
			// An input event waiting: start a new pipeline with this event
			event = m_inQueue.poll();
			is_pulled = m_isPulled.poll();
		}
		m_inQueueLock.unlock();
		if (m_pipelines.size() >= m_maxPipelines)
		{
			// Indicates the maximum number of pipelines is reached
			to_return = false;
		}
		if (event != null && m_pipelines.size() < m_maxPipelines)
		{
			Object[] inputs = new Object[1];
			inputs[0] = event;
			PipelineRunnable new_pipeline = new PipelineRunnable(m_processor.clone(), inputs, is_pulled);			
			m_pipelinesLock.lock();
			m_pipelines.add(new_pipeline);
			m_pipelinesLock.unlock();
			ManagedThread new_thread = null;
			if (m_threadManager != null)
			{
				new_thread = m_threadManager.tryNewThread(new_pipeline);
			}
			if (new_thread != null)
			{
				// We got a thread: run pipeline in that thread
				new_pipeline.setThread(new_thread);
				new_thread.start();
			}
			else
			{
				// No thread: run pipeline in the current thread
				new_pipeline.run();
			}
		}
		else
		{

		}
		m_pipelinesLock.lock();
		if (!m_pipelines.isEmpty())
		{
			PipelineRunnable pt = m_pipelines.getFirst();
			if (!pt.getIsPulled())
			{
				while (pt.hasEvent())
				{
					// If this thread has been started from pushed events,
					// must push whatever it produces
					Object o = shiftEntries();
					m_outputPushable.push(o);
					m_outputPushable.waitFor();
				}
			}
		}
		m_pipelinesLock.unlock();
		return to_return;
	}
}
