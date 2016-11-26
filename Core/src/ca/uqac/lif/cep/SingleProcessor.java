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
package ca.uqac.lif.cep;

import java.util.ArrayDeque;
import java.util.Iterator;
import java.util.Queue;

/**
 * Performs a computation on input events to produce output events.
 * <p>
 * This is the direct descendant of {@link Processor}, and probably the one
 * you'll want to inherit from when creating your own processors. While
 * {@link Processor} takes care of input and output queues,
 * {@link SingleProcessor} also implements {@link Pullable}s and
 * {@link Pushable}s. These take care of collecting input events, waiting
 * until one new event is received from all input traces before triggering
 * the computation, pulling and buffering events from all outputs when
 * either of the {@link Pullable}s is being called, etc.
 * <p>
 * The only thing that is left undefined is what to do
 * when new input events have been received from all input traces. This
 * is the task of abstract method {@link #compute(Object[])}, which descendants
 * of this class must implement.
 *   
 * @author Sylvain Hallé
 *
 */
public abstract class SingleProcessor extends Processor
{
	/**
	 * Initializes a processor
	 * @param in_arity The input arity
	 * @param out_arity The output arity
	 */
	public SingleProcessor(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
	}

	@Override
	public final Pushable getPushableInput(int index)
	{
		return new InputPushable(index);
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		if (index >= 0 && index < m_outputArity)
		{
			return new OutputPullable(index);
		}
		return null;
	}

	/**
	 * Computes one or more output events from its input events
	 * @param inputs An array of input events; its length corresponds to the
	 *   processor's input arity
	 * @return A queue of vectors of output events, or null
	 *   if no event could be produced
	 */
	protected abstract Queue<Object[]> compute(Object[] inputs);

	/**
	 * Implementation of a {@link Pushable} for a single processor.
	 * 
	 * @author Sylvain Hallé
	 */
	protected class InputPushable implements Pushable
	{
		/**
		 * The index of the processor's input this pushable refers to
		 */
		private final int m_index;

		/**
		 * Creates a pushable associated to some of a processor's input
		 * traces. 
		 * @param index The index of the trace. Should be between 0 and
		 *   the processor's input arity - 1. This is not checked by the
		 *   constructor, so beware.
		 */
		InputPushable(int index)
		{
			super();
			m_index = index;
		}
		
		@Override
		public Pushable pushFast(Object o)
		{
			return push(o);
		}
				
		@Override
		public int getPosition()
		{
			return m_index;
		}

		@Override
		public Pushable push(Object o)
		{
			if (m_index < m_inputQueues.length)
			{
				Queue<Object> q = m_inputQueues[m_index];
				q.add(o);
			}
			// Check if each input queue has an event ready
			for (int i = 0; i < m_inputArity; i++)
			{
				Queue<Object> queue = m_inputQueues[i];
				if (queue.isEmpty())
				{
					// One of them doesn't: we can't produce an output yet
					return this;
				}
			}
			// Pick an event from each input queue
			Object[] inputs = new Object[m_inputArity];
			for (int i = 0; i < m_inputArity; i++)
			{
				Queue<Object> queue = m_inputQueues[i];
				Object ob = queue.remove();
				inputs[i] = ob;
			}
			// Compute output event
			Queue<Object[]> outs = compute(inputs);
			if (outs != null && !outs.isEmpty())
			{
				for (Object[] evt : outs)
				{
					if (evt != null)
					{
						//assert evt.length >= m_outputPushables.size();
						for (int i = 0; i < m_outputPushables.length; i++)
						{
							Pushable p = m_outputPushables[i];
							assert p != null;
							p.push(evt[i]);
							p.waitFor();
						}
					}
				}
			}
			return this;
		}

		@Override
		public Processor getProcessor() 
		{
			return SingleProcessor.this;
		}

		@Override
		public void waitFor() 
		{
			// Since this pushable is blocking
			return;
		}
	}

	/**
	 * Implementation of a {@link Pullable} for a single processor.
	 * 
	 * @author Sylvain Hallé
	 */
	protected class OutputPullable implements Pullable
	{
		/**
		 * The index of the processor's output this pullable refers to
		 */
		private final int m_index;

		/**
		 * Creates a pullable associated to some of a processor's output
		 * traces. 
		 * @param index The index of the trace. Should be between 0 and
		 *   the processor's output arity - 1. This is not checked by the
		 *   constructor, so beware.
		 */
		public OutputPullable(int index)
		{
			super();
			m_index = index;
		}
		
		@Override
		public void remove()
		{
			// Cannot remove an event on a pullable
			throw new UnsupportedOperationException();
		}
		
		@Override
		public Object pullSoft()
		{
			if (hasNextSoft() != NextStatus.YES)
			{
				return null;
			}
			Queue<Object> out_queue = m_outputQueues[m_index];
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
		public Object pull()
		{
			if (hasNext() != true)
			{
				return null;
			}				
			Queue<Object> out_queue = m_outputQueues[m_index];
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
		public final Object next()
		{
			return pull();
		}

		@Override
		public boolean hasNext()
		{
			Queue<Object> out_queue = m_outputQueues[m_index];
			// If an event is already waiting in the output queue,
			// return it and don't pull anything from the input
			if (!out_queue.isEmpty())
			{
				return true;
			}
			// Check if each pullable has an event ready
			for (int tries = 0; tries < Pullable.s_maxRetries; tries++)
			{
				for (int i = 0; i < m_inputArity; i++)
				{
					Pullable p = m_inputPullables[i];
					assert p != null;
					boolean status = p.hasNext();
					if (status == false)
					{
						return false;
					}
				}
				// We are here only if every input pullable has answered YES
				// Pull an event from each
				Object[] inputs = new Object[m_inputArity];
				for (int i = 0; i < m_inputArity; i++)
				{
					Pullable p = m_inputPullables[i];
					Object o = p.pull();
					inputs[i] = o;
				}
				// Compute output event(s)
				Queue<Object[]> computed = compute(inputs);
				NextStatus status_to_return = NextStatus.NO;
				if (computed == null)
				{
					// No output will ever be returned: stop there
					return false;
				}
				if (!computed.isEmpty())
				{
					// We computed an output event; add it to the output queue
					// and answer YES
					for (Object[] evt : computed)
					{
						if (evt != null)
						{
							for (int i = 0; i < m_outputArity; i++)
							{
								Queue<Object> queue = m_outputQueues[i];
								queue.add(evt[i]);
							}
							status_to_return = NextStatus.YES;
						}
						else
						{
							// This source will NEVER output anything again
							return false;
						}
					}
					if (status_to_return == NextStatus.YES)
					{
						return true;
					}
				}
				// Otherwise, try the whole thing again
			}
			return false;
		}

		@Override
		public NextStatus hasNextSoft()
		{
			Queue<Object> out_queue = m_outputQueues[m_index];
			// If an event is already waiting in the output queue,
			// return yes and don't pull anything from the input
			if (!out_queue.isEmpty())
			{
				return NextStatus.YES;
			}
			// Check if each pullable has an event ready
			for (int i = 0; i < m_inputArity; i++)
			{
				Pullable p = m_inputPullables[i];
				NextStatus status = p.hasNextSoft();
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
			Object[] inputs = new Object[m_inputArity];
			{
				int i = 0;
				for (Pullable p : m_inputPullables)
				{
					inputs[i] = p.pullSoft();
					i++;
				}
			}
			// Compute output event(s)
			NextStatus status_to_return = NextStatus.MAYBE;
			Queue<Object[]> computed = compute(inputs);
			if (computed == null)
			{
				status_to_return = NextStatus.NO;
			}
			else if (!computed.isEmpty())
			{
				for (Object[] evt : computed)
				{
					if (evt != null)
					{
						// We computed an output event; add it to the output queue
						// and answer YES
						int i = 0;
						for (Queue<Object> queue : m_outputQueues)
						{
							queue.add(evt[i]);
							i++;
						}
						status_to_return = NextStatus.YES;
					}
				}
			}
			return status_to_return;
		}
		
		@Override
		public Processor getProcessor() 
		{
			return SingleProcessor.this;
		}

		@Override
		public int getPosition() 
		{
			return m_index;
		}

		@Override
		public Iterator<Object> iterator()
		{
			return this;
		}
	}
	
	/**
	 * Puts an array of objects (given as an argument) into an
	 * empty queue of arrays of objects. This is a convenience method
	 * that descendants of {@link SingleProcessor} (which implement
	 * {@link #compute(Object[])}) can use to avoid
	 * a few lines of code when they output a single array of events. 
	 * @param v The array of objects
	 * @return The queue, or <code>null</code> if all elements of
	 *   <code>v</code> are null
	 */
	protected static final Queue<Object[]> wrapVector(Object[] v)
	{
		if (v == null || allNull(v))
		{
			return null;
		}
		Queue<Object[]> out = newQueue();
		out.add(v);
		return out;
	}
	
	/**
	 * Puts a object (given as an argument) into an
	 * empty queue of arrays of objects. This is a convenience method
	 * that descendants of {@link SingleProcessor} (which implement
	 * {@link #compute(Object[])}) can use to avoid
	 * a few lines of code when they output a single event. 
	 * @param o The object
	 * @return The queue
	 */
	protected static final Queue<Object[]> wrapObject(Object o)
	{
		Queue<Object[]> out = newQueue();
		Object[] v = new Object[1];
		v[0] = o;
		out.add(v);
		return out;
	}
	
	/**
	 * Gets a new instance of an empty object queue
	 * @return The queue
	 */
	public static Queue<Object[]> newQueue()
	{
		return new ArrayDeque<Object[]>();
	}
	
}
