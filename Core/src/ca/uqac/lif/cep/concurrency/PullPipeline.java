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
	 * Semaphore to stop the pipeline
	 */
	protected boolean m_run = false;
	
	/**
	 * The maximum number of simultaneous threads that this pipeline
	 * can use
	 */
	protected int m_maxThreads = 2;
	
	/**
	 * Time to wait before polling again
	 */
	protected static final long s_sleepInterval = 50;
	
	/**
	 * The processor that will be pipelined
	 */
	protected Processor m_processor;
	
	public PullPipeline(Processor p)
	{
		super(1, 1);
		m_inQueue = new LinkedList<Object>();
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
		m_context.putAll(context);
		m_processor.setContext(context);
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		m_context.put(key, value);
		m_processor.setContext(key, value);
	}
	
	/**
	 * Shifts the index of each entry of the out map by -1 
	 */
	protected Object shiftEntries()
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
		public Object pullSoft() 
		{
			if (m_threads.isEmpty())
			{
				return null;
			}
			Object out = shiftEntries();
			return out;
		}

		@Override
		public Object pull() 
		{
			if (!m_threads.isEmpty() && m_threads.getFirst().hasEvent())
			{
				Object out = shiftEntries();
				return out;
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
					return null;
				}
				if (!m_threads.isEmpty() && m_threads.getFirst().hasEvent())
				{
					Object out = shiftEntries();
					return out;
				}
			}
		}

		@Override
		public Object next() 
		{
			return pull();
		}

		@Override
		public NextStatus hasNextSoft()
		{
			if (m_threads.isEmpty())
			{
				return NextStatus.MAYBE;
			}
			return NextStatus.YES;
		}

		@Override
		public boolean hasNext() 
		{
			if (!m_threads.isEmpty() && m_threads.getFirst().hasEvent())
			{
				return true;
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
				if (!m_threads.isEmpty() && m_threads.getFirst().hasEvent())
				{
					return true;
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
		public Pushable push(Object o)
		{
			m_inQueue.add(o);
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
	}
	
	class PipelineThread extends Thread
	{	
		Object[] m_inputs;
		
		Queue<Object> m_outQueue;
		
		PipelineThread(Object[] inputs)
		{
			super();
			m_inputs = inputs;
			m_outQueue = new LinkedList<Object>();
		}
		
		public Object popEvent()
		{
			return m_outQueue.remove();
		}
		
		public boolean hasEvent()
		{
			return !m_outQueue.isEmpty();
		}
		
		public boolean canDelete()
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
					m_outQueue.add(o);
				}
			} 
			catch (ConnectorException e)
			{
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}

	@Override
	public void run()
	{
		m_run = true;
		while (m_run)
		{
			Object o = m_inputPullable.pullSoft();
			if (o != null)
			{
				m_inQueue.add(o);
				doThreadHousekeeping();
			}
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
		Thread t = new Thread(this);
		t.start();
	}
	
	@Override
	public void stop()
	{
		m_run = false;
	}
	
	protected void doThreadHousekeeping()
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
			Object[] inputs = new Object[1];
			inputs[0] = event;
			PipelineThread new_thread = new PipelineThread(inputs);
			m_threads.add(new_thread);
			new_thread.start();
		}
	}
}
