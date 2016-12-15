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

import java.util.LinkedList;
import java.util.Queue;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.NextStatus;

class ContinuousPoller implements Poller
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
	protected static final long s_sleepDuration = 10;

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
					//System.out.println("NOT NULL");
					//synchronized (this)
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
				Thread.currentThread().interrupt();
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
		if (m_events.isEmpty())
		{
			return NextStatus.MAYBE;
		}
		return NextStatus.YES;
	}

	@Override
	public boolean getNextHardStatus()
	{
		if (m_events.isEmpty())
		{
			while (true)
			{
				ThreadManager.sleep(s_sleepDuration);
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

	@Override
	public Object getNextSoft()
	{
		if (m_events.isEmpty())
		{
			return false;
		}
		return m_events.remove();
	}

	@Override
	public Object getNextHard()
	{
		if (m_events.isEmpty())
		{
			while (true)
			{
				ThreadManager.sleep(s_sleepDuration);
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

	@Override
	public void dispose()
	{
		stop();
		m_pullable.dispose();
	}

}
