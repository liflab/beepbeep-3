/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2025 Sylvain Hallé

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

import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.Stateful;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

/**
 * Source whose input is a queue of objects. One gives the
 * {@code QueueSource} a list of events, and that source sends these events
 * as its input one by one. When reaching the end of the list, the source
 * returns to the beginning and keeps feeding events from the list endlessly.
 * This behaviour can be changed with {@link #loop(boolean)}.
 * 
 * @author Sylvain Hallé
 * @since 0.1
 */
@SuppressWarnings("squid:S2160")
public class QueueSource extends Source implements Stateful
{
	/**
	 * The events to repeat endlessly
	 */
	protected List<Object> m_events;

	/**
	 * Whether to loop over the events endlessly
	 */
	protected boolean m_loop = true;

	/**
	 * The index of the next event to produce
	 */
	protected int m_index;

	/**
	 * Creates a new queue source of given output arity. The events of the queue
	 * source will be duplicated on each of the outputs.
	 * 
	 * @param arity
	 *          The output arity
	 */
	public QueueSource(int arity)
	{
		super(arity);
		m_events = new ArrayList<Object>();
		m_index = 0;
	}

	/**
	 * Creates a new queue source of output arity 1.
	 */
	public QueueSource()
	{
		super(1);
		m_events = new ArrayList<Object>();
		m_index = 0;
	}

	/**
	 * Creates a new queue source of output arity 1, and populates it with a list
	 * of objects.
	 * @param queue A collection of events that the queue source will output. If the
	 *          collection is ordered, the events will be output in the order they
	 *          appear in the collection.
	 * @since 0.10.9
	 */
	public QueueSource(Collection<? extends Object> queue)
	{
		this(1);
		for (Object o : queue)
		{
			m_events.add(o);
		}
	}

	/**
	 * Sets the events that the queue will output.
	 * 
	 * @param queue
	 *          A collection of events that the queue source will output. If the
	 *          collection is ordered, the events will be output in the order they
	 *          appear in the collection.
	 */
	public void setEvents(Collection<Object> queue)
	{
		m_events.clear();
		for (Object o : queue)
		{
			m_events.add(o);
		}
	}

	/**
	 * Sets the events that the queue will output
	 * 
	 * @param queue
	 *          An array of events that the queue source will output. The events
	 *          will be output in the order they appear in the collection.
	 * @return This queue source
	 */
	public QueueSource setEvents(Object ... queue)
	{
		m_events.clear();
		for (Object o : queue)
		{
			m_events.add(o);
		}
		return this;
	}

	/**
	 * Adds an event to the queue
	 * 
	 * @param e
	 *          The event to add
	 * @return This queue source
	 */
	public QueueSource addEvent(Object e)
	{
		m_events.add(e);
		return this;
	}

	/**
	 * Sets whether to loop over the events endlessly
	 * 
	 * @param b
	 *          Set to {@code true} to loop over the events endlessly
	 *          (default), or {@code false} to play them only once.
	 * @return This queue source
	 */
	public QueueSource loop(boolean b)
	{
		m_loop = b;
		return this;
	}

	@Override
	@SuppressWarnings("squid:S1168")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		int size = m_events.size();
		if (m_index >= size)
		{
			return false;
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
		if (m_index > size && !m_loop)
		{
			// No more events from this queue
			return false;
		}
		for (int i = 0; i < getOutputArity(); i++)
		{
			if (event == null)
			{
				// If one of the elements is null, don't output anything
				return true;
			}
			output[i] = event;
		}
		outputs.add(output);
		return true;
	}

	@Override
	public void reset()
	{
		super.reset();
		m_index = 0;
	}

	@Override
	public QueueSource duplicate(boolean with_state)
	{
		QueueSource out = new QueueSource(getOutputArity());
		out.m_loop = m_loop;
		out.setEvents(m_events);
		if (with_state)
		{
			out.m_index = m_index;
		}
		return out;
	}

	@Override
	public Class<?> getOutputType(int index)
	{
		// We return the type of the first non-null object in the queue
		for (Object o : m_events)
		{
			if (o != null)
			{
				return o.getClass();
			}
		}
		return Variant.class;
	}

	/**
	 * @since 0.10.2
	 */
	@Override
	public Object printState()
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put("index", m_index);
		map.put("loop", m_loop);
		map.put("events", m_events);
		return map;
	}

	/**
	 * @since 0.10.2
	 */
	@SuppressWarnings("unchecked")
	@Override
	public QueueSource readState(Object o)
	{
		Map<String,Object> map = (Map<String,Object>) o;
		QueueSource qs = new QueueSource();
		qs.m_index = ((Number) map.get("index")).intValue();
		qs.m_events = (List<Object>) map.get("events");
		qs.m_loop = (Boolean) map.get("loop");
		return qs;
	}

	/**
	 * @since 0.11
	 */
	@Override
	public Object getState()
	{
		return m_index;
	}
}
