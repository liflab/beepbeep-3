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

public class CountDecimate extends SingleProcessor
{
	/**
	 * The decimation interval
	 */
	protected final int m_interval;
	
	/**
	 * Index of last event received
	 */
	protected int m_current;
	
	public CountDecimate(int interval)
	{
		super(1, 1);
		m_interval = interval;
		m_current = 0;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_current = 0;
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		Vector<Object> out = null;
		if (m_current == 0)
		{
			out = inputs;
		}
		m_current = (m_current + 1) % m_interval;
		return wrapVector(out);
	}

}
