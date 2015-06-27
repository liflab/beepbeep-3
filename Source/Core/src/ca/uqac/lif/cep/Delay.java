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

import java.util.Queue;
import java.util.Vector;

public class Delay extends SingleProcessor
{
	/**
	 * How many events to ignore at the beginning of the trace
	 */
	protected final int m_delay;
	
	/**
	 * The number of events received so far
	 */
	protected int m_eventsReceived;
	
	public Delay()
	{
		this(0);
	}
	
	public Delay(int delay)
	{
		super(1, 1);
		m_delay = delay;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_eventsReceived = 0;
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		m_eventsReceived++;
		if (m_eventsReceived > m_delay)
		{
			return wrapVector(inputs);
		}
		return null;
	}

}
