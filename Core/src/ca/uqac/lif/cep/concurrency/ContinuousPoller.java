package ca.uqac.lif.cep.concurrency;

import java.util.LinkedList;
import java.util.Queue;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.NextStatus;

public class ContinuousPoller implements Poller
{
	private boolean m_run = false;

	private boolean m_done = false;

	volatile Queue<Object> m_events;

	/**
	 * The Pullable this poller will pull events from
	 */
	private Pullable m_pullable;

	/**
	 * If the queue reaches this size, the poller temporarily
	 * stops pulling new events from its Pullable until some of
	 * them are consumed
	 */
	protected static final long s_maxQueueSize = 100;

	/**
	 * Sleep interval (in milliseconds) between calls to the pullable's
	 * pull method
	 */
	protected static final long s_sleepDuration = 100;

	public ContinuousPoller(Pullable p)
	{
		super();
		m_events = new LinkedList<Object>();
		m_pullable = p;
	}

	@Override
	public void run() 
	{
		m_run = true;
		while (m_run)
		{
			if (m_events.size() < s_maxQueueSize)
			{
				m_done = false;
				Object o = m_pullable.pullSoft();
				if (o != null)
				{
					synchronized (m_events)
					{
						m_events.add(o);
					}				
				}
				m_done = true;				
			}
			try 
			{
				Thread.sleep(s_sleepDuration);
			} 
			catch (InterruptedException e) 
			{
				m_run = false;
			}
		}
	}

	@Override
	public boolean isDone()
	{
		return m_done;
	}

	@Override
	public void call(Call c) 
	{
		// Do nothing
	}

	@Override
	public NextStatus getNextSoftStatus() 
	{
		synchronized (m_events)
		{
			if (m_events.isEmpty())
			{
				return NextStatus.MAYBE;
			}
			return NextStatus.YES;
		}
	}

	@Override
	public boolean getNextHardStatus() 
	{
		synchronized (m_events)
		{
			if (m_events.isEmpty())
			{
				while (true)
				{
					OnDemandPoller.sleep(s_sleepDuration);
					if (!m_events.isEmpty())
					{
						// As long as the thread is running, wait for
						// an event to be added to the queue
						return true;
					}
					if (!m_run)
					{
						// The thread stopped running, meaning no more events ever
						return false;
					}
				}
			}
			return true;
		}
	}

	@Override
	public Object getNextSoft() 
	{
		synchronized (m_events)
		{
			if (m_events.isEmpty())
			{
				return false;
			}
			return m_events.remove();
		}
	}

	@Override
	public Object getNextHard() 
	{
		synchronized (m_events)
		{
			if (m_events.isEmpty())
			{
				while (true)
				{
					OnDemandPoller.sleep(s_sleepDuration);
					if (!m_events.isEmpty())
					{
						// As long as the thread is running, wait for
						// an event to be added to the queue
						return m_events.remove();
					}
					if (!m_run)
					{
						// The thread stopped running, meaning no more events ever
						return null;
					}
				}
			}
			else
			{
				return m_events.remove();
			}
		}
	}

	@Override
	public void stop() 
	{
		m_run = false;
	}

	@Override
	public Pullable getPullable() 
	{
		return m_pullable;
	}

}
