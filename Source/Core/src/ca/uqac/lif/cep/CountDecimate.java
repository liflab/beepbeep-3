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

/**
 * Returns one input event and discards the next <i>n</i>-1. The value <i>n</i>
 * is called the <em>decimation interval</em>.
 * 
 * @author Sylvain Hallé
 */
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
	
	public CountDecimate()
	{
		this(1);
	}
	
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
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object[] out = null;
		if (m_current == 0)
		{
			out = inputs;
		}
		m_current = (m_current + 1) % m_interval;
		return wrapVector(out);
	}
	
	public static void build(Stack<Object> stack)
	{
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // OF
		stack.pop(); // TH
		Number interval = (Number) stack.pop();
		stack.pop(); // EVERY
		CountDecimate out = new CountDecimate(interval.intValue());
		Connector.connect(p, out);
		stack.push(out);
	}
}
