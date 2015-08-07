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

public abstract class SingleProcessor extends Processor
{

	public SingleProcessor()
	{
		super();
	}
	
	/**
	 * Initializes a processor
	 * @param in_arity The input arity
	 * @param out_arity The output arity
	 */
	public SingleProcessor(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_inputPullables = new Vector<Pullable>(m_inputArity);
		m_outputPushables = new Vector<Pushable>(m_outputArity);
		reset();
	}

	@Override
	public final void setPullableInput(int i, Pullable p)
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

	@Override
	public final Pushable getPushableOutput(int index)
	{
		return m_outputPushables.get(index);
	}

	@Override
	public final void setPushableOutput(int i, Pushable p)
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


	@Override
	public void reset()
	{
		initializeInput();
		initializeOutput();
	}

	@Override
	public final Pushable getPushableInput(int index)
	{
		return new InputPushable(index);
	}

	@Override
	public final Pullable getPullableOutput(int index)
	{
		return new OutputPullable(index);
	}

	public void start()
	{
		// Do nothing by default
	}

	/**
	 * Computes one or more output events from its input events
	 * @param inputs A vector of input events; its length corresponds to the
	 *   processor's input arity
	 * @return A queue of vectors of output events, or null
	 *   if no event could be produced
	 */
	protected abstract Queue<Vector<Object>> compute(Vector<Object> inputs);

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
			Queue<Vector<Object>> outs = compute(inputs);
			if (outs != null && !outs.isEmpty())
			{
				for (Vector<Object> evt : outs)
				{
					if (evt != null && !evt.isEmpty())
					{
						assert evt.size() >= m_outputPushables.size();
						for (int i = 0; i < m_outputPushables.size(); i++)
						{
							Pushable p = m_outputPushables.get(i);
							p.push(evt.get(i));
						}
					}
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
			if (hasNext() != NextStatus.YES)
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
		public synchronized Object pullHard()
		{
			if (hasNextHard() != NextStatus.YES)
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

		public synchronized NextStatus hasNextHard()
		{
			Queue<Object> out_queue = m_outputQueues.get(m_index);
			// If an event is already waiting in the output queue,
			// return it and don't pull anything from the input
			if (!out_queue.isEmpty())
			{
				return NextStatus.YES;
			}
			// Check if each pullable has an event ready
			for (long tries = 0; tries < Pullable.s_maxRetries; tries++)
			{
				for (int i = 0; i < m_inputArity; i++)
				{
					Pullable p = m_inputPullables.get(i);
					NextStatus status = p.hasNextHard();
					if (status == NextStatus.NO)
					{
						return NextStatus.NO;
					}
				}
				// We are here only if every input pullable has answered YES
				// Pull an event from each
				Vector<Object> inputs = new Vector<Object>();
				for (int i = 0; i < m_inputArity; i++)
				{
					Pullable p = m_inputPullables.get(i);
					Object o = p.pullHard();
					inputs.add(o);
				}
				// Compute output event(s)
				Queue<Vector<Object>> computed = compute(inputs);
				NextStatus status_to_return = NextStatus.NO;
				if (computed != null && !computed.isEmpty())
				{
					// We computed an output event; add it to the output queue
					// and answer YES
					for (Vector<Object> evt : computed)
					{
						if (evt != null && !evt.isEmpty())
						{
							for (int i = 0; i < m_outputArity; i++)
							{
								Queue<Object> queue = m_outputQueues.get(i);
								queue.add(evt.get(i));
							}
							status_to_return = NextStatus.YES;
						}
					}
					if (status_to_return == NextStatus.YES)
					{
						return NextStatus.YES;
					}
				}
				// Otherwise, try the whole thing again
			}
			return NextStatus.NO;
		}

		@Override
		public synchronized NextStatus hasNext()
		{
			Queue<Object> out_queue = m_outputQueues.get(m_index);
			// If an event is already waiting in the output queue,
			// return it and don't pull anything from the input
			if (!out_queue.isEmpty())
			{
				return NextStatus.YES;
			}
			// Check if each pullable has an event ready
			for (int i = 0; i < m_inputArity; i++)
			{
				Pullable p = m_inputPullables.get(i);
				NextStatus status = p.hasNextHard();
				if (status == NextStatus.NO)
				{
					return NextStatus.NO;
				}
				if (status == NextStatus.MAYBE)
				{
					return NextStatus.MAYBE;
				}
			}
			// We are here only if every input pullable has answered YES
			// Pull an event from each
			Vector<Object> inputs = new Vector<Object>();
			for (int i = 0; i < m_inputArity; i++)
			{
				Pullable p = m_inputPullables.get(i);
				Object o = p.pull();
				inputs.add(o);
			}
			// Compute output event(s)
			NextStatus status_to_return = NextStatus.MAYBE;
			Queue<Vector<Object>> computed = compute(inputs);
			if (computed != null && !computed.isEmpty())
			{
				for (Vector<Object> evt : computed)
				{
					if (evt != null && !evt.isEmpty())
					{
						// We computed an output event; add it to the output queue
						// and answer YES
						for (int i = 0; i < m_outputArity; i++)
						{
							Queue<Object> queue = m_outputQueues.get(i);
							queue.add(evt.get(i));
						}
						status_to_return = NextStatus.YES;
					}
				}
			}
			return status_to_return;
		}
	}
	
	protected static final Queue<Vector<Object>> wrapVector(Vector<Object> v)
	{
		Queue<Vector<Object>> out = new LinkedList<Vector<Object>>();
		out.add(v);
		return out;
	}
	
	protected static final Queue<Vector<Object>> wrapObject(Object o)
	{
		Queue<Vector<Object>> out = new LinkedList<Vector<Object>>();
		Vector<Object> v = new Vector<Object>();
		v.add(o);
		out.add(v);
		return out;
	}
	
}
