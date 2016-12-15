package ca.uqac.lif.cep.concurrency;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.concurrency.ThreadManager.ManagedThread;

/**
 * Pushable that launches the {@link Pushable#push(Object) push()} call in
 * a new thread if one is available.
 * 
 * @author Sylvain Hallé
 */
public class NewThreadPushable implements Pushable
{
	/**
	 * The pushable that will push events to the original pushable
	 */
	protected Pushable m_pushable;

	/**
	 * The thread manager that will give threads to this pushable
	 */
	private ThreadManager m_manager;

	/**
	 * The thread that is currently running the push
	 */
	private ManagedThread m_currentThread;

	/**
	 * The reference to the processor
	 */
	private Processor m_processorReference;

	NewThreadPushable(Processor reference, Pushable pushable, ThreadManager manager)
	{
		super();
		m_processorReference = reference;
		m_pushable = pushable;
		m_manager = manager;
	}

	@Override
	public Pushable push(Object o)
	{
		m_pushable.push(o);
		return this;
	}

	@Override
	public synchronized Pushable pushFast(Object o)
	{
		PushRunnable pr = new PushRunnable(o);
		ManagedThread thread = m_manager.tryNewThread(pr);
		if (thread == null)
		{
			// No thread: just push normally
			m_currentThread = null;
			synchronized (m_pushable)
			{
				m_pushable.push(o);
			}
		}
		else
		{
			// Got a thread: keep it and start it
			m_currentThread = thread;
			m_currentThread.start();
		}
		return this;
	}

	@Override
	public Processor getProcessor()
	{
		return m_processorReference;
	}

	@Override
	public int getPosition()
	{
		return 0;
	}

	@Override
	public synchronized void waitFor()
	{
		if (m_currentThread == null)
		{
			// We don't have a thread, so just return
			return;
		}
		try
		{
			m_currentThread.join();
		}
		catch (InterruptedException e)
		{
			// Should be OK
			Thread.currentThread().interrupt();
		}
		m_currentThread.dispose();
		m_currentThread = null;
	}

	@Override
	public void dispose()
	{
		if (m_currentThread != null)
		{
			m_currentThread.dispose();
		}
		m_currentThread = null;
	}

	protected class PushRunnable implements Runnable
	{
		/**
		 * The event that will be pushed to the internal pushable
		 */
		private final Object m_eventToPush;

		public PushRunnable(Object event)
		{
			super();
			m_eventToPush = event;
		}

		@Override
		public void run()
		{
			m_pushable.push(m_eventToPush);
		}
	}

}
