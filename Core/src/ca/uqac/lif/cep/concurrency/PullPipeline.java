package ca.uqac.lif.cep.concurrency;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Queue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.tmf.QueueSource;

public class PullPipeline extends Processor implements Runnable
{
	/**
	 * A queue of incoming messages
	 */
	protected Queue<Object> m_inQueue;

	/**
	 * A matching queue of Booleans; an entry contains the value
	 * true if the event of <code>m_inQueue</code> was pulled from
	 * the input, and false if it was pushed from it
	 */
	protected Queue<Boolean> m_isPulled;

	/**
	 * A "queue" of threads
	 */
	protected LinkedList<PipelineThread> m_threads;

	/**
	 * The pullable the pipeline will read from
	 */
	protected Pullable m_inputPullable;

	/**
	 * The pushable the pipeline will push to
	 */
	protected Pushable m_outputPushable;
	
	/**
	 * The pushable one can push to this pipeline
	 */
	protected Pushable m_inputPushable;

	/**
	 * Semaphore to stop the pipeline
	 */
	protected boolean m_run = false;

	/**
	 * The maximum number of simultaneous threads that this pipeline
	 * can use
	 */
	protected int m_maxThreads = 1;

	/**
	 * Time (in milliseconds) to wait before polling again
	 */
	protected static final long s_sleepInterval = 1000;

	/**
	 * The processor that will be pipelined
	 */
	protected Processor m_processor;

	public PullPipeline(Processor p)
	{
		super(1, 1);
		m_inQueue = new LinkedList<Object>();
		m_isPulled = new LinkedList<Boolean>();
		m_threads = new LinkedList<PipelineThread>();
		m_processor = p;
	}

	@Override
	public void setPullableInput(int index, Pullable p)
	{
		if (index == 0)
		{
			m_inputPullable = p;
		}
	}

	@Override
	public void setPushableOutput(int index, Pushable p)
	{
		if (index == 0)
		{
			m_outputPushable = p;
		}
	}

	@Override
	public Pushable getPushableInput(int index) 
	{
		return new PipelinePushable();
	}

	@Override
	public Pullable getPullableOutput(int index) 
	{
		return new PipelinePullable();
	}

	@Override
	public PullPipeline clone() 
	{
		PullPipeline p = new PullPipeline(m_processor.clone());
		p.setContext(m_context);
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
	 * Shifts the index of each entry of the out map by -1 
	 */
	synchronized protected Object shiftEntries()
	{
		// Entry 0 is guaranteed to be here if this method is called
		PipelineThread thread = m_threads.get(0);
		Object o = thread.popEvent();
		if (thread.canDelete())
		{
			// This thread is done; we remove it
			m_threads.remove(0);
		}
		return o;
	}

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
			// Not implemented at the moment
			return null;
		}

		@Override
		synchronized public Object pullSoft() 
		{
			if (m_threads.isEmpty())
			{
				return null;
			}
			Object out = shiftEntries();
			return out;
		}

		@Override
		synchronized public Object pull() 
		{
			if (!m_threads.isEmpty() && m_threads.getFirst().hasEvent())
			{
				Object out = shiftEntries();
				return out;
			}
			// Wait until index 0 appears
			while (m_run)
			{
				try 
				{
					Thread.sleep(s_sleepInterval);
				} 
				catch (InterruptedException e) 
				{
					return null;
				}
				if (!m_threads.isEmpty() && m_threads.getFirst().hasEvent())
				{
					Object out = shiftEntries();
					return out;
				}
			}
			return null;
		}

		@Override
		synchronized public Object next() 
		{
			return pull();
		}

		@Override
		synchronized public NextStatus hasNextSoft()
		{
			if (!m_run)
			{
				return NextStatus.NO;
			}
			if (m_threads.isEmpty())
			{
				return NextStatus.MAYBE;
			}
			return NextStatus.YES;
		}

		@Override
		public boolean hasNext() 
		{
			if (!m_run)
			{
				return false;
			}
			synchronized (m_threads)
			{
				if (!m_threads.isEmpty() && m_threads.getFirst().hasEvent())
				{
					return true;
				}
			}
			// Wait until index 0 appears
			while (true)
			{
				try 
				{
					Thread.sleep(s_sleepInterval);
				} 
				catch (InterruptedException e) 
				{
					return false;
				}
				synchronized (m_threads)
				{
					if (!m_threads.isEmpty() && m_threads.getFirst().hasEvent())
					{
						System.out.println("Has event");
						return true;
					}					
				}
			}
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
		public boolean isDone() 
		{
			return true;
		}
	}

	class PipelineThread extends Thread
	{	
		Object[] m_inputs;

		Queue<Object> m_outQueue;

		boolean m_isPulled;

		PipelineThread(Object[] inputs, boolean is_pulled)
		{
			super();
			m_inputs = inputs;
			m_outQueue = new LinkedList<Object>();
			m_isPulled = is_pulled;
		}

		synchronized public Object popEvent()
		{
			return m_outQueue.remove();
		}

		synchronized public boolean hasEvent()
		{
			return !m_outQueue.isEmpty();
		}

		synchronized public boolean canDelete()
		{
			return m_outQueue.isEmpty() && !isAlive();
		}

		@Override
		public void run()
		{
			Processor p = m_processor.clone();
			QueueSource qs = new QueueSource();
			qs.loop(false);
			qs.addEvent(m_inputs[0]);
			try 
			{
				Connector.connect(qs, p);
				Pullable pullable = p.getPullableOutput();
				while (pullable.hasNext())
				{
					Object o = pullable.pull();
					synchronized (this)
					{
						System.out.println("PUTTING " + o);
						m_outQueue.add(o);
					}
				}
			} 
			catch (ConnectorException e)
			{
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			System.out.println("DONE");
		}
	}

	@Override
	public void run()
	{
		m_run = true;
		while (m_run)
		{
			if (m_threads.size() < m_maxThreads)
			{
				Object o = m_inputPullable.pullSoft();
				if (o != null)
				{
					synchronized (this)
					{
						m_inQueue.add(o);	
					}
				}				
			}
			doThreadHousekeeping();
			try 
			{
				Thread.sleep(s_sleepInterval);
			} 
			catch (InterruptedException e) 
			{
				m_run = false;
				break;
			}
		}
	}

	@Override
	public void start()
	{
		if (!m_run)
		{
			System.out.println("START");
			Thread t = new Thread(this);
			t.start();
		}
	}

	@Override
	public void stop()
	{
		m_run = false;
	}

	synchronized protected void doThreadHousekeeping()
	{
		int num_running = 0;
		for (PipelineThread pt : m_threads)
		{
			if (pt.isAlive())
			{
				num_running++;
			}
		}
		if (num_running < m_maxThreads && !m_inQueue.isEmpty())
		{
			// We have room for a new running thread, and there is
			// an input event waiting: start a new thread with this event
			Object event = m_inQueue.poll();
			boolean is_pulled = m_isPulled.poll();
			Object[] inputs = new Object[1];
			inputs[0] = event;
			PipelineThread new_thread = new PipelineThread(inputs, is_pulled);
			m_threads.add(new_thread);
			new_thread.start();
		}
		if (!m_threads.isEmpty())
		{
			PipelineThread pt = m_threads.getFirst();
			while (!pt.m_isPulled && pt.hasEvent())
			{
				// If this thread has been started from pushed events,
				// must push whatever it produces
				Object o = shiftEntries();
				m_outputPushable.push(o);
			}
		}
	}
}
