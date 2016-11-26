package ca.uqac.lif.cep.concurrency;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.concurrency.Pusher.Call;

public class ThreadPushable implements Pushable
{	
	protected Pusher m_pusher;
	
	protected Thread m_thread;
	
	protected static final long s_sleepDuration = 100;
	
	public ThreadPushable(Pusher p)
	{
		super();
		m_pusher = p;
		m_thread = new Thread(m_pusher);
		m_thread.start();
	}
	
	public void start()
	{
		m_thread.start();
	}
	
	public void stop()
	{
		m_pusher.stop();
	}

	@Override
	public Pushable push(Object o) 
	{
		m_pusher.setEventToPush(o);
		m_pusher.call(Call.PUSH);
		return this;
	}

	@Override
	public Processor getProcessor() 
	{
		return m_pusher.getPushable().getProcessor();
	}

	@Override
	public int getPosition() 
	{
		return m_pusher.getPushable().getPosition();
	}

	@Override
	public void waitFor() 
	{
		m_pusher.waitFor();
	}

}
