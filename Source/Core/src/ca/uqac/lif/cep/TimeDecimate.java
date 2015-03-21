/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

import java.util.Vector;

public class TimeDecimate extends SingleProcessor
{
	/**
	 * Interval of time
	 */
	protected final long m_interval;
	
	/**
	 * The system time when the last event was output
	 */
	protected long m_timeLastSent;
	
	public TimeDecimate(long interval)
	{
		super(1, 1);
		m_interval = interval;
		m_timeLastSent = -1;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_timeLastSent = -1;
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		Vector<Object> out = null;
		if (m_timeLastSent < 0)
		{
			out = inputs;
		}
		else
		{
			long current_time = System.nanoTime();
			long time_dif = current_time - m_timeLastSent;
			if (time_dif >= m_interval)
			{
				out = inputs;
			}
		}
		return out;
	}

}
