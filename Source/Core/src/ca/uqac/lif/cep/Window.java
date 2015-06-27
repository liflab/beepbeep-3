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

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

/**
 * Simulates the application of a "sliding window" to a trace.
 * <ul>
 * <li>The processor takes as arguments another processor &phi; and a
 *  window width <i>n</i></li>
 * <li>It returns the result of &phi; after processing events 0 to
 *   <i>n</i>-1...</li>
 * <li>Then the result of (a new instance of &phi;) that processes
 *   events 1 to <i>n</i>-1...</li>
 * <li>...and so on</li> 
 * </ul>
 * @author sylvain
 *
 */
public class Window extends SingleProcessor
{
	/**
	 * The window's width
	 */
	protected int m_width;
	
	/**
	 * The internal processor
	 */
	protected Processor m_processor = null;
	
	/**
	 * The internal processor's input pushables
	 */
	protected Vector<Pushable> m_innerInputs = null;
	
	/**
	 * The sink that will receive the events produced by the inner processor
	 */
	protected QueueSink m_sink = null;
	
	/**
	 * The event windows
	 */
	protected Vector<List<Object>> m_window;
	
	public Window()
	{
		super();
	}
	
	public Window(Processor in_processor, int width)
	{
		super(in_processor.getInputArity(), in_processor.getOutputArity());
		m_width = width;
		m_processor = in_processor;
		m_sink = new QueueSink(in_processor.getOutputArity());
		reset();
	}
	
	@Override
	public void reset()
	{
		super.reset();
		int arity = getInputArity();
		m_window = new Vector<List<Object>>(arity);
		m_innerInputs = new Vector<Pushable>(arity);
		if (m_processor != null)
		{
			m_processor.reset();
			for (int i = 0; i < arity; i++)
			{
				m_window.add(new LinkedList<Object>());
				m_innerInputs.add(m_processor.getPushableInput(i));
			}		
		}
		if (m_sink != null)
		{
			m_sink.reset();
		}
		if (m_processor != null && m_sink != null)
		{
			Connector.connect(m_processor, m_sink);
		}
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		// Add the inputs to each window
		boolean windows_ok = true;
		int arity = inputs.size();
		for (int i = 0; i < arity; i++)
		{
			List<Object> q = m_window.get(i);
			q.add(inputs.get(i));
			int size_diff = q.size() - m_width;
			leftTrim(size_diff, q);
			if (size_diff < 0)
			{
				// Window is still to small to compute
				windows_ok = false;
			}
		}
		Vector<Object> out = null;
		if (windows_ok) // All windows have the proper width
		{
			m_processor.reset();
			m_sink.reset();
			for (int i = 0; i < m_width; i++)
			{
				for (int j = 0; j < getInputArity(); j++)
				{
					// Feed 
					List<Object> q = m_window.get(j);
					Object o = q.get(i);
					Pushable p = m_innerInputs.get(j);
					p.push(o);
				}
				out = m_sink.remove();
			}
		}
		return wrapVector(out);
	}
	
	/**
	 * Trims <i>n</i> events from the beginning of <tt>q</tt>
	 * @param n The number of events to trim. If <i>n</i>&nbsp;&lt;1,
	 *   trims nothing. If <i>n</i> is larger than the list's size,
	 *   empties the list
	 * @param q The queue to trim
	 */
	protected static void leftTrim(int n, List<Object> q)
	{
		if (n <= 0)
		{
			return;
		}
		if (n >= q.size())
		{
			q.clear();
			return;
		}
		for (int i = 0; i < n; i++)
		{
			q.remove(0);
		}
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		Number width = (Number) stack.pop();
		Processor p = (Processor) stack.pop();
		Window out = new Window(p, width.intValue());
		stack.push(out);
	}

}
