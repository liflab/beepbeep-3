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
package ca.uqac.lif.cep.tmf;

import java.util.Queue;
import java.util.Vector;

/**
 * Source whose input is a queue of objects. One gives the
 * <code>QueueSource</code> a list of events, and that source sends
 * these events as its input one by one. When reaching the end of
 * the list, the source returns to the beginning and keeps feeding
 * events from the list endlessly. This behaviour can be changed
 * with {@link #loop(boolean)}.
 * 
 * @author Sylvain Hallé
 */
public class QueueSource extends Source
{
	/**
	 * The events to repeat endlessly
	 */
	protected Vector<Object> m_events;
	
	/**
	 * Whether to loop over the events endlessly
	 */
	protected boolean m_loop = true;
	
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
	
	public QueueSource(int arity)
	{
		super(arity);
		m_events = new Vector<Object>();
		m_index = 0;
	}
	
	public void setEvents(Vector<Object> queue)
	{
		m_events = queue;
	}
	
	/**
	 * Sets whether to loop over the events endlessly
	 * @param b Set to <code>true</code> to loop over the events
	 * endlessly (default), or <code>false</code> to play them
	 * only once.
	 * @return This queue source
	 */
	public QueueSource loop(boolean b)
	{
		m_loop = b;
		return this;
	}
	
	/*@Override
	public Pullable getPullableOutput(int index)
	{
		return new SentinelPullable(index);
	}*/

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		int size = m_events.size();
		if (m_index >= size)
		{
			return null;
		}
		Object[] output = new Object[getOutputArity()];
		Object event = m_events.get(m_index);
		if (m_loop)
		{
			m_index = (m_index + 1) % size;
		}
		else
		{
			// If we don't loop, play the events only once
			m_index++;
		}
		for (int i = 0; i < getOutputArity(); i++)
		{
			output[i] = event;
		}
		return wrapVector(output);
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_index = 0;
	}
	
	@Override
	public QueueSource clone()
	{
		QueueSource out = new QueueSource(null, getOutputArity());
		out.setEvents(m_events);
		return out;
	}
}
