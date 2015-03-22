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
import java.util.Stack;
import java.util.Vector;

public class QueueSource extends Source
{
	/**
	 * The events to repeat endlessly
	 */
	protected final Vector<Object> m_events;
	
	/**
	 * The index of the next event to produce
	 */
	protected int m_index;
	
	public QueueSource()
	{
		super();
		m_events = new Vector<Object>();
		m_index = 0;
	}
	
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
		m_events.addAll(o);
		m_index = 0;
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		Vector<Object> output = new Vector<Object>();
		Object event = m_events.get(m_index);
		m_index = (m_index + 1) % m_events.size();
		for (int i = 0; i < getOutputArity(); i++)
		{
			output.add(event);
		}
		return wrapVector(output);
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		QueueSource out = new QueueSource(o, 1);
		stack.push(out);
	}
}
