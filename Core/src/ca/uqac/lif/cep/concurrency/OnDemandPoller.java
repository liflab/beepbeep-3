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
		ThreadManager.sleep(s_sleepInterval);
	}

	@Override
	synchronized public void stop()
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
