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

import ca.uqac.lif.cep.Pushable;

public class OnDemandPusher implements Pusher
{
	protected Pushable m_pushable;

	boolean m_run = false;

	protected long s_sleepInterval = 0;

	private Call m_currentCall = Call.NONE;

	private Object m_eventToPush = null;

	private boolean m_done = false;

	public OnDemandPusher(Pushable p)
	{
		super();
		m_pushable = p;
	}

	@Override
	public void dispose()
	{
		m_pushable.dispose();
	}

	@Override
	public void run()
	{
		m_run = true;
		while (m_run)
		{
			switch (m_currentCall)
			{
			case PUSH:
				m_done = false;
				m_pushable.pushFast(m_eventToPush);
				m_eventToPush = null;
				break;
			default:
				break;
			}
			m_currentCall = Call.NONE;
			m_done = true;
			ThreadManager.sleep(s_sleepInterval);
		}
	}

	@Override
	public void setEventToPush(Object o)
	{
		m_eventToPush = o;
	}

	@Override
	public void waitFor()
	{
		while (!m_done)
		{
			ThreadManager.sleep(s_sleepInterval);
		}
	}

	@Override
	public void call(Call c)
	{
		m_done = false;
		m_currentCall = c;
	}

	@Override
	public void stop()
	{
		m_run = false;
	}

	@Override
	public Pushable getPushable()
	{
		return m_pushable;
	}

}
