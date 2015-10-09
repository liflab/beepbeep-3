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

public class QueueSource extends Source
{
	/**
	 * The events to repeat endlessly
	 */
	protected Vector<Object> m_events;
	
	/**
	 * The index of the next event to produce
	 */
	protected int m_index;
	
	public QueueSource(Object o, int arity)
	{
		super(arity);
		m_events = new Vector<Object>();
		m_events.add(o);
		m_index = 0;
	}
	
	public QueueSource(Queue<Object> o, int arity)
	{
		super(arity);
		m_events = new Vector<Object>();
		if (o != null)
		{
			m_events.addAll(o);
		}
		m_index = 0;
	}
	
	public void setEvents(Vector<Object> queue)
	{
		m_events = queue;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object[] output = new Object[getOutputArity()];
		Object event = m_events.get(m_index);
		m_index = (m_index + 1) % m_events.size();
		if (event == null)
		{
			return null;
		}
		for (int i = 0; i < getOutputArity(); i++)
		{
			output[i] = event;
		}
		return wrapVector(output);
	}

}
