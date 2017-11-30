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

/**
 * Sink that remembers only the last event sent to it. This event can
 * be queried with {@link #getLast()}.
 * 
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class SinkLast extends Sink
{
	/**
	 * The last event (or array of events) received
	 */
	protected Object[] m_last;

	/**
	 * The number of events received so far
	 */
	protected int m_eventCounter;

	public SinkLast()
	{
		super();
		m_last = null;
		m_eventCounter = 0;
	}

	public SinkLast(int in_arity)
	{
		super(in_arity);
		m_last = null;
		m_eventCounter = 0;
	}

	@Override
	public void reset()
	{
		super.reset();
		m_last = null;
		m_eventCounter = 0;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		m_last = inputs;
		return true;
	}

	public Object[] getLast()
	{
		return m_last;
	}

	@Override
	public SinkLast duplicate()
	{
		return new SinkLast(getInputArity());
	}
}
