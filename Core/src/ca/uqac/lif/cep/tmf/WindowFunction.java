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

import java.util.LinkedList;
import java.util.Queue;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionException;

/**
 * Takes a sliding window of <i>n</i> successive input events,
 * passes them to an <i>n</i>-ary function and outputs the result.
 * This currently only works for functions with an output arity of 1.
 * @see Window
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2160")
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
	protected LinkedList<Object> m_window;

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
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		m_window.add(inputs[0]);
		int size = m_window.size();
		if (size == m_width + 1)
		{
			m_window.remove(0);
			Object[] val = new Object[1];
			try
			{
				m_function.evaluate(m_window.toArray(), val);
			}
			catch (FunctionException e)
			{
				throw new ProcessorException(e);
			}
			outputs.add(wrapObject(val[0]));
			return true;
		}
		if (size == m_width)
		{
			Object[] val = new Object[1];
			try
			{
				m_function.evaluate(m_window.toArray(), val);
			}
			catch (FunctionException e)
			{
				throw new ProcessorException(e);
			}
			outputs.add(wrapObject(val[0]));
			return true;
		}
		return true;
	}

	@Override
	public WindowFunction duplicate()
	{
		WindowFunction wf = new WindowFunction(m_function.duplicate());
		wf.m_window.addAll(m_window);
		return wf;
	}
}
