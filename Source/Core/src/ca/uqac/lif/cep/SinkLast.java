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

/**
 * Sink that remembers only the last event sent to it. This event can
 * be queried with {@link #getLast()}.
 * 
 * @author Sylvain Hallé
 *
 */
class SinkLast extends Sink
{
	protected Object[] m_last;
	
	public SinkLast(int in_arity)
	{
		super(in_arity);
		m_last = null;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_last = null;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		m_last = inputs;
		return null;
	}
	
	public Object[] getLast()
	{
		return m_last;
	}
	
	public Object getQueue(int i)
	{
		if (m_last == null)
		{
			return null;
		}
		return m_last[i];
	}
}
