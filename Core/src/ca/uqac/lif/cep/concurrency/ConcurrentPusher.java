package ca.uqac.lif.cep.concurrency;

import java.util.Iterator;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.tmf.SinkLast;

public class ConcurrentPusher extends Processor
{
	private Processor m_processor;
	private Pushable m_processorPushable;

	protected QueuePoller[] m_pollers;

	protected Thread[] m_threads;

	private boolean m_done = false;

	protected SinkLast m_sink;

	public ConcurrentPusher(Processor p, int num_threads)
	{
		super(1, 1);
		m_processor = p;
		m_sink = new SinkLast();
		try 
		{
			Connector.connect(m_processor, m_sink);
		} 
		catch (ConnectorException e) 
		{
			e.printStackTrace();
		}
		m_processorPushable = p.getPushableInput();
		m_pollers = new QueuePoller[num_threads];
		m_threads = new Thread[num_threads];
		for (int i = 0; i < num_threads; i++)
		{
			m_pollers[i] = new QueuePoller();
			m_threads[i] = new Thread(m_pollers[i]);
		}
	}

	@Override
	public void start()
	{
		for (int i = 0; i < m_threads.length; i++)
		{
			m_threads[i].start();
		}
		int thread_num = 0;
		int num_pulled = 0;
		while (m_inputPullables[0].hasNext() != false)
		{
			Object o = m_inputPullables[0].next();
			m_pollers[thread_num].put(o);
			thread_num = (thread_num + 1) % m_threads.length;
			num_pulled++;
		}
		System.out.println("Pulled: " + num_pulled);
		m_done = true;
	}

	@Override
	public void stop()
	{
		for (int i = 0; i < m_threads.length; i++)
		{
			m_pollers[i].stop();
		}
	}

	@Override
	public Pushable getPushableInput(int index) 
	{
		// Cannot push to this processor
		return new DummyPushable();
	}

	@Override
	public Pullable getPullableOutput(int index) 
	{
		return new SentinelPullable();
	}

	@Override
	public Processor clone() 
	{
		// Don't clone processors that manage threads
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Pushable that does nothing
	 */
	protected class DummyPushable implements Pushable
	{

		@Override
		public Pushable push(Object o) throws PushableException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Pushable pushFast(Object o) throws PushableException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Processor getProcessor() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public int getPosition() {
			// TODO Auto-generated method stub
			return 0;
		}

		@Override
		public void waitFor() {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void dispose() {
			// TODO Auto-generated method stub
			
		}
		
	}

	protected class SentinelPullable implements Pullable
	{
		protected boolean m_eventSent = false;

		public SentinelPullable()
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
		public Object pullSoft()
		{
			if (m_eventSent)
			{
				return null;
			}
			if (!m_done)
			{
				return null;
			}
			m_eventSent = true;
			return m_sink.getLast()[0];
		}

		@Override
		@SuppressWarnings("squid:S1168")
		public Object pull()
		{
			if (m_eventSent)
			{
				return null;
			}
			return m_sink.getLast()[0];
		}

		@Override
		public final Object next()
		{
			return pull();
		}

		@Override
		public NextStatus hasNextSoft()
		{
			if (m_done && m_eventSent)
			{
				return NextStatus.NO;
			}
			if (!m_done)
			{
				return NextStatus.MAYBE;
			}
			return NextStatus.YES;
		}

		@Override
		public boolean hasNext()
		{
			if (m_done && m_eventSent)
			{
				return false;
			}
			while (!m_done)
			{
				try
				{
					Thread.sleep(1);
				} 
				catch (InterruptedException e)
				{
					// TODO Auto-generated catch block
					e.printStackTrace();
					return false;
				}
			}
			return true;
		}

		@Override
		public Processor getProcessor()
		{
			return ConcurrentPusher.this;
		}

		@Override
		public int getPosition()
		{
			return m_inputPullables[0].getPosition();
		}

		@Override
		public Iterator<Object> iterator()
		{
			return this;
		}

		@Override
		public void start()
		{
			for (Pullable p : m_inputPullables)
			{
				p.start();
			}
		}

		@Override
		public void stop()
		{
			for (Pullable p : m_inputPullables)
			{
				p.stop();
			}
		}

		@Override
		public void dispose()
		{
			for (Pullable p : m_inputPullables)
			{
				p.dispose();
			}
		}
	}

	protected class QueuePoller implements Runnable
	{
		private boolean m_run;

		private Queue<Object> m_queue;

		public QueuePoller()
		{
			super();
			m_run = true;
			m_queue = new ConcurrentLinkedQueue<Object>();
		}

		public void stop()
		{
			m_run = false;
		}

		public void put(Object o)
		{
			m_queue.add(o);
		}

		@Override
		public void run()
		{
			while (m_run)
			{
				if (!m_queue.isEmpty())
				{
					Object o = m_queue.poll();
					m_processorPushable.push(o);
				}
			}
		}
	}
}
