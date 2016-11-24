package ca.uqac.lif.cep.concurrency;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.NextStatus;

class OnDemandPoller implements Poller 
{
	protected Pullable m_pullable;
	
	boolean m_run = false;

	protected long s_sleepInterval = 100;

	private Call m_currentCall = Call.NONE;
	
	private NextStatus m_lastSoftStatus;
	
	private boolean m_lastHardStatus;
	
	private boolean m_done;
	
	private Object m_lastEvent;

	public OnDemandPoller(Pullable p)
	{
		super();
		m_pullable = p;
		m_done = true;
	}
	
	@Override
	synchronized public boolean isDone()
	{
		return m_done;
	}
	
	@Override
	synchronized public void call(Call c)
	{
		m_done = false;
		m_currentCall = c;
	}
	
	@Override
	synchronized public NextStatus getNextSoftStatus()
	{
		return m_lastSoftStatus;
	}
	
	@Override
	synchronized public boolean getNextHardStatus()
	{
		return m_lastHardStatus;
	}
	
	@Override
	synchronized public Object getNextSoft()
	{
		return m_lastEvent;
	}
	
	@Override
	synchronized public Object getNextHard()
	{
		return m_lastEvent;
	}

	@Override
	public void run() 
	{
		m_run = true;
		while (m_run)
		{
			switch (m_currentCall)
			{
			case HAS_NEXT:
				m_lastHardStatus = m_pullable.hasNext();
				break;
			case HAS_NEXT_SOFT:
				m_lastSoftStatus = m_pullable.hasNextSoft();
				break;
			case PULL_SOFT:
				m_lastEvent = m_pullable.pullSoft();
				break;
			case PULL:
				m_lastEvent = m_pullable.pull();
				break;
			default:
				break;
			}
			m_currentCall = Call.NONE;
			m_done = true;
		}
		sleep(s_sleepInterval);
	}
	
	@Override
	synchronized public void stop()
	{
		m_run = false;
	}
	
	public static void sleep(long duration)
	{
		try
		{
			Thread.sleep(duration);
		}
		catch (InterruptedException e)
		{
			// Do nothing
		}		
	}

	@Override
	public Pullable getPullable() 
	{
		return m_pullable;
	}

}
