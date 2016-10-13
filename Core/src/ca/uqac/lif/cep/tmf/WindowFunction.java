/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hall�

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

import java.util.ArrayDeque;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.functions.Function;

/**
 * Takes a sliding window of <i>n</i> successive input events,
 * passes them to an <i>n</i>-ary function and outputs the result.
 * This currently only works for functions with an output arity of 1.
 * @author Sylvain Hallé
 */
public class WindowFunction extends SingleProcessor
{
	/**
	 * The window's width
	 */
	protected int m_width;

	/**
	 * The internal function
	 */
	protected Function m_function;
	
	/**
	 * The event window
	 */
	protected List<Object> m_window;

	WindowFunction()
	{
		this(1);
	}
	
	WindowFunction(int width)
	{
		super(1, 1);
		m_window = new LinkedList<Object>();
		m_width = width;
	}
	
	/**
	 * Creates a new Window from a given function
	 * @param f The function. Its output arity must be exactly 1.
	 */
	public WindowFunction(/*@NonNull*/ Function f)
	{
		this(f.getInputArity());
		m_function = f;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs) 
	{
		m_window.add(inputs[0]);
		int size = m_window.size();
		if (size == m_width + 1)
		{
			m_window.remove(0);
			Object value = m_function.evaluate(m_window.toArray())[0];
			return wrapObject(value);
		}
		if (size == m_width)
		{
			Object value = m_function.evaluate(m_window.toArray())[0];
			return wrapObject(value);
		}
		return new ArrayDeque<Object[]>();
	}

	@Override
	public WindowFunction clone()
	{
		return new WindowFunction(m_function);
	}
}
