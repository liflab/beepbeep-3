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
import ca.uqac.lif.cep.concurrency.ThreadManager.ManagedThread;

public class ThreadPushable implements Pushable
{
	/**
	 * The pusher that will push events to the original pushable
	 */
	protected Pusher m_pusher;

	/**
	 * The managed thread in which this pullable is running, if any
	 */
	protected ManagedThread m_thread = null;

	/**
	 * The interval (in milliseconds) between polls to the internal
	 * pushable
	 */
	protected static final long s_sleepDuration = 0;

	/**
	 * Attempts to get an instance of thread pushable. The method will
	 * ask for a thread from the thread manager; if no thread can be
	 * given, the method will return the original (blocking) pushable.
	 * @param push The original pushable
	 * @param manager The thread manager
	 * @return A new thread pushable or the original pushable
	 */
	synchronized public static Pushable tryPushable(Pushable push, ThreadManager manager)
	{
		if (manager == null)
		{
			return push;
		}
		Pusher odp = new OnDemandPusher(push);
		ManagedThread t = manager.tryNewThread(odp);
		if (t == null)
		{
			return push;
		}
		return new ThreadPushable(odp, t);
	}

	/**
	 * Attempts to get an instance of thread pushable. The method will
	 * ask for a thread from the default thread manager; if no thread can be
	 * given, the method will return the original (blocking) pushable.
	 * @param push The original pushable
	 * @return A new thread pushable or the original pushable
	 */
	public static Pushable tryPushable(Pushable push)
	{
		return tryPushable(push, ThreadManager.defaultManager);
	}

	private ThreadPushable(Pusher p, ManagedThread t)
	{
		super();
		m_pusher = p;
		m_thread = t;
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

	@Override
	public void dispose()
	{
		stop();
		m_pusher.dispose();
		if (m_thread != null)
		{
			m_thread.dispose();
		}
	}

}
