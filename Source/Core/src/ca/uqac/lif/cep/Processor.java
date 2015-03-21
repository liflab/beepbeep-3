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
import java.util.Queue;
import java.util.Vector;

public abstract class Processor
{
	protected Vector<Queue<Object>> m_inputQueues;
	
	protected Vector<Queue<Object>> m_outputQueues;
	
	protected Vector<Pullable> m_inputPullables;
	
	protected Vector<Pushable> m_outputPushables;
	
	/**
	 * The processor's input arity, i.e. the number of input events it requires
	 * to produce an output
	 */
	protected final int m_inputArity;
	
	/**
	 * The processor's output arity, i.e. the number of output
	 * events it produces
	 */
	protected final int m_outputArity;
	
	/**
	 * Initializes a processor
	 * @param in_arity The input arity
	 * @param out_arity The output arity
	 */
	Processor(int in_arity, int out_arity)
	{
		super();
		m_inputArity = in_arity;
		m_outputArity = out_arity;
		m_inputPullables = new Vector<Pullable>(m_inputArity);
		m_outputPushables = new Vector<Pushable>(m_outputArity);
		reset();
	}
	
	/**
	 * Returns the processor's input arity
	 * @return The arity
	 */
	public final int getInputArity()
	{
		return m_inputArity;
	}
	
	/**
	 * Returns the processor's output arity
	 * @return The arity
	 */
	public final int getOutputArity()
	{
		return m_outputArity;
	}
	
	public void setPullableInput(int i, Pullable p)
	{
		if (i == m_inputPullables.size())
		{
			m_inputPullables.add(p);
		}
		else
		{
			m_inputPullables.set(i, p);
		}
	}
	
	public Pushable getPushableOutput(int index)
	{
		return m_outputPushables.get(index);
	}
	
	public void setPushableOutput(int i, Pushable p)
	{
		if (i == m_outputPushables.size())
		{
			m_outputPushables.add(p);
		}
		else
		{
			m_outputPushables.set(i, p);	
		}
	}
	
	protected final void initializeInput()
	{
		m_inputQueues = new Vector<Queue<Object>>();
		for (int i = 0; i < m_inputArity; i++)
		{
			m_inputQueues.add(new LinkedList<Object>());
		}
	}
	
	protected final void initializeOutput()
	{
		m_outputQueues = new Vector<Queue<Object>>();
		for (int i = 0; i < m_outputArity; i++)
		{
			m_outputQueues.add(new LinkedList<Object>());
		}
	}
	
	/**
	 * Resets the processor. This has for effect of flushing the contents
	 * of all input and output event queues. If the processor has an internal
	 * state, this also resets this state to its "initial" settings.
	 */
	public void reset()
	{
		initializeInput();
		initializeOutput();
	}
	
	public final Pushable getPushableInput(int index)
	{
		return new InputPushable(index);
	}
	
	public final Pullable getPullableOutput(int index)
	{
		return new OutputPullable(index);
	}
	
	public void start()
	{
		// Do nothing by default
	}
	
	/**
	 * Computes an output event from its input events
	 * @param inputs A vector of input events; its length corresponds to the
	 *   processor's input arity
	 * @return A vector of output events, or null if no event could be produced
	 */
	protected abstract Vector<Object> compute(Vector<Object> inputs);
	
	protected class InputPushable implements Pushable
	{
		/**
		 * The index of the processor's input this pushable refers to
		 */
		protected final int m_index;
		
		InputPushable(int index)
		{
			super();
			m_index = index;
		}
		
		@Override
		public synchronized void push(Object o)
		{
			Queue<Object> q = m_inputQueues.get(m_index);
			q.add(o);
			// Check if each input queue has an event ready
			for (int i = 0; i < m_inputArity; i++)
			{
				Queue<Object> queue = m_inputQueues.get(i);
				if (queue.isEmpty())
				{
					// One of them doesn't: we can't produce an output yet
					return;
				}
			}
			// Pick an event from each input queue
			Vector<Object> inputs = new Vector<Object>();
			for (int i = 0; i < m_inputArity; i++)
			{
				Queue<Object> queue = m_inputQueues.get(i);
				Object ob = queue.remove();
				inputs.add(ob);
			}
			// Compute output event
			Vector<Object> outs = compute(inputs);
			if (outs != null && !outs.isEmpty())
			{
				assert outs.size() >= m_outputPushables.size();
				for (int i = 0; i < m_outputPushables.size(); i++)
				{
					Pushable p = m_outputPushables.get(i);
					p.push(outs.get(i));
				}
			}
		}
	}
	
	protected class OutputPullable implements Pullable
	{
		/**
		 * The index of the processor's output this pullable refers to
		 */
		protected final int m_index;
		
		public OutputPullable(int index)
		{
			super();
			m_index = index;
		}
		
		@Override
		public synchronized Object pull()
		{
			if (!hasNext())
			{
				return null;
			}
			Queue<Object> out_queue = m_outputQueues.get(m_index);
			// If an event is already waiting in the output queue,
			// return it and don't pull anything from the input
			if (!out_queue.isEmpty())
			{
				Object o = out_queue.remove();
				return o;
			}
			return null;
		}
		
		@Override
		public synchronized boolean hasNext()
		{
			Queue<Object> out_queue = m_outputQueues.get(m_index);
			// If an event is already waiting in the output queue,
			// return it and don't pull anything from the input
			if (!out_queue.isEmpty())
			{
				return true;
			}
			// Check if each pullable has an event ready
			for (int i = 0; i < m_inputArity; i++)
			{
				Pullable p = m_inputPullables.get(i);
				if (!p.hasNext())
				{
					// One of them doesn't: we can't produce an output
					return false;
				}
			}
			// Pull an event from each input pullable
			Vector<Object> inputs = new Vector<Object>();
			for (int i = 0; i < m_inputArity; i++)
			{
				Pullable p = m_inputPullables.get(i);
				Object o = p.pull();
				inputs.add(o);
			}
			// Compute output event(s)
			Vector<Object> computed = compute(inputs);
			if (computed == null || computed.isEmpty())
			{
				return false;
			}
			for (int i = 0; i < m_outputArity; i++)
			{
				Queue<Object> queue = m_outputQueues.get(i);
				queue.add(computed.get(i));
			}
			return true;
		}
	}
	
}
