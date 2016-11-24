package ca.uqac.lif.cep.concurrency;

import java.util.Iterator;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.concurrency.Poller.Call;

public class ThreadPullable implements Pullable
{
	protected Poller m_poller;
	
	protected Thread m_thread;
	
	protected static final long s_sleepDuration = 100;
	
	public ThreadPullable(Poller p)
	{
		super();
		m_poller = p;
		m_thread = new Thread(m_poller);
	}
	
	public void start()
	{
		m_thread.start();
	}
	
	public void stop()
	{
		m_poller.stop();
	}

	@Override
	public Iterator<Object> iterator() 
	{
		// Don't use a threadpullable as an iterator
		return null;
	}

	@Override
	public Object pullSoft() 
	{
		m_poller.call(Call.PULL_SOFT);
		while (!m_poller.isDone())
		{
			OnDemandPoller.sleep(s_sleepDuration);
		}
		return m_poller.getNextSoft();
	}

	@Override
	public Object pull() 
	{
		m_poller.call(Call.PULL);
		while (!m_poller.isDone())
		{
			OnDemandPoller.sleep(s_sleepDuration);
		}
		Object out = m_poller.getNextHard();
		//System.out.println("OUT: " + out);
		return out;
	}

	@Override
	public Object next() 
	{
		return pull();
	}

	@Override
	public NextStatus hasNextSoft() 
	{
		m_poller.call(Call.HAS_NEXT_SOFT);
		while (!m_poller.isDone())
		{
			OnDemandPoller.sleep(s_sleepDuration);
		}
		return m_poller.getNextSoftStatus();
	}

	@Override
	public boolean hasNext() 
	{
		m_poller.call(Call.HAS_NEXT);
		while (!m_poller.isDone())
		{
			OnDemandPoller.sleep(s_sleepDuration);
		}
		boolean status = m_poller.getNextHardStatus();
		return status;
	}

	@Override
	public Processor getProcessor() 
	{
		return m_poller.getPullable().getProcessor();
	}

	@Override
	public int getPosition() 
	{
		return m_poller.getPullable().getPosition();
	}

}
