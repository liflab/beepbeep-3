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

import java.util.Iterator;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.concurrency.Poller.Call;
import ca.uqac.lif.cep.concurrency.ThreadManager.ManagedThread;

public class ThreadPullable implements Pullable
{
	/**
	 * The poller that will repeatedly poll the input pullable
	 */
	protected Poller m_poller;

	/**
	 * The managed thread in which this pullable is running, if any
	 */
	protected ManagedThread m_thread = null;

	/**
	 * The interval (in milliseconds) between polls to the input pullable
	 */
	protected static final long s_sleepDuration = 100;

	/**
	 * Attempts to get an instance of thread pullable. The method will
	 * ask for a thread from the thread manager; if no thread can be
	 * given, the method will return the original (blocking) pullable.
	 * @param pull The original pullable
	 * @param manager The thread manager
	 * @return A new thread pullable or the original pullable
	 */
	public static Pullable tryPullable(Pullable pull, ThreadManager manager)
	{
		if (manager == null)
		{
			return pull;
		}
		Poller poll = new ContinuousPoller(pull);
		ManagedThread t = manager.tryNewThread(poll);
		if (t == null)
		{
			return pull;
		}
		return new ThreadPullable(poll, t);
	}

	/**
	 * Attempts to get an instance of thread pullable. The method will
	 * ask for a thread from the default thread manager; if no thread can be
	 * given, the method will return the original (blocking) pullable.
	 * @param pull The original pullable
	 * @return A new thread pullable or the original pullable
	 */
	public static Pullable tryPullable(Pullable pull)
	{
		return tryPullable(pull, ThreadManager.defaultManager);
	}

	private ThreadPullable(Poller p, ManagedThread t)
	{
		super();
		m_poller = p;
		m_thread = t;
	}

	@Override
	public void start()
	{
		m_thread.start();
	}

	@Override
	public void stop()
	{
		m_poller.stop();
		m_thread.dispose();
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
			ThreadManager.sleep(s_sleepDuration);
		}
		return m_poller.getNextSoft();
	}

	@Override
	public Object pull()
	{
		m_poller.call(Call.PULL);
		while (!m_poller.isDone())
		{
			ThreadManager.sleep(s_sleepDuration);
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
			ThreadManager.sleep(s_sleepDuration);
		}
		return m_poller.getNextSoftStatus();
	}

	@Override
	public boolean hasNext()
	{
		m_poller.call(Call.HAS_NEXT);
		while (!m_poller.isDone())
		{
			ThreadManager.sleep(s_sleepDuration);
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

	@Override
	public void remove()
	{
		// Do nothing
	}

	@Override
	public void dispose()
	{
		stop();
		m_poller.dispose();
		if (m_thread != null)
		{
			m_thread.dispose();
		}
	}

}
