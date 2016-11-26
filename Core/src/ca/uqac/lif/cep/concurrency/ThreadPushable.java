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
	public Pushable pushFast(Object o) 
	{
		m_pusher.setEventToPush(o);
		m_pusher.call(Call.PUSH);
		return this;
	}
	
	@Override
	public Pushable push(Object o) 
	{
		m_pusher.setEventToPush(o);
		m_pusher.call(Call.PUSH);
		m_pusher.waitFor();
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
