/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2023 Sylvain Hallé

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
import java.util.NoSuchElementException;
import java.util.Queue;

/**
 * Performs a computation on input events to produce output events.
 * 
 * This is the direct descendant of {@link Processor}, and probably the one
 * you'll want to inherit from when creating your own processors. While
 * {@link Processor} takes care of input and output queues,
 * {@link SynchronousProcessor} also implements {@link Pullable}s and
 * {@link Pushable}s. These take care of collecting input events, waiting until
 * one new event is received from all input traces before triggering the
 * computation, pulling and buffering events from all outputs when either of the
 * {@link Pullable}s is being called, etc.
 * <p>
 * The only thing that is left undefined is what to do when new input events
 * have been received from all input traces. This is the task of abstract method
 * {@link #compute(Object[], Queue)}, which descendants of this class must
 * implement.
 * <p>
 * In early versions of the library, this class was called
 * {@code SingleProcessor}.
 * 
 * @author Sylvain Hallé
 * @since 0.1
 *
 */
@SuppressWarnings("squid:S2160")
public abstract class SynchronousProcessor extends Processor
{
	/**
	 * A queue object that will be passed to the {@link #compute(Object[], Queue)}
	 * method
	 */
	protected final transient Queue<Object[]> m_tempQueue;

	/**
	 * An array of input pushables
	 */
	protected final transient Pushable[] m_inputPushables;

	/**
	 * An array of output pullables
	 */
	protected transient Pullable[] m_outputPullables;

	/**
	 * Initializes a processor
	 * 
	 * @param in_arity
	 *          The input arity
	 * @param out_arity
	 *          The output arity
	 */
	public SynchronousProcessor(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_tempQueue = new ArrayDeque<Object[]>(1);
		m_inputPushables = new Pushable[in_arity];
		m_outputPullables = new Pullable[out_arity];
	}

	@Override
	public Pushable getPushableInput(int index)
	{
		if (m_inputPushables[index] == null)
		{
			m_inputPushables[index] = new InputPushable(index);
		}
		return m_inputPushables[index];
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		if (m_outputPullables[index] == null)
		{
			m_outputPullables[index] = new OutputPullable(index);
		}
		return m_outputPullables[index];
	}

	/**
	 * Computes one or more output events from its input events
	 * 
	 * @param inputs
	 *          An array of input events; its length corresponds to the processor's
	 *          input arity
	 * @param outputs
	 *          A queue of arrays of objects. The processor should push arrays into
	 *          this queue for every output front it produces. The size of each
	 *          array should be equal to the processor's output arity, although this
	 *          is not enforced.
	 * @return {@code true} if this processor may output other events in the
	 * future, {@code false} otherwise
	 */
	protected abstract boolean compute(Object[] inputs, Queue<Object[]> outputs);

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
		 * Creates a pushable associated to some of a processor's input traces.
		 * 
		 * @param index
		 *          The index of the trace. Should be between 0 and the processor's
		 *          input arity - 1. This is not checked by the constructor, so beware.
		 */
		InputPushable(int index)
		{
			super();
			m_index = index;
		}

		@Override
		public int getPosition()
		{
			return m_index;
		}

		@Override
		public Pushable push(Object o)
		{
			try
			{
				Queue<Object> q = m_inputQueues[m_index];
				q.add(o);
			}
			catch (ArrayIndexOutOfBoundsException e)
			{
				throw new PushableException(e);
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
			m_tempQueue.clear();
			boolean outs;
			try
			{
				outs = compute(inputs, m_tempQueue);
			}
			catch (ProcessorException e)
			{
				throw new PushableException(e);
			}
			// put everything in outputEvent, because of duplicated code in notifyEndOfTrace
			outputEvent(outs);
			return this;
		}

		@Override
		public void notifyEndOfTrace()
		{
			m_hasBeenNotifiedOfEndOfTrace[m_index] = true;
			if (m_notifiedEndOfTraceDownstream || !allNotifiedEndOfTrace())
			{
				return;
			}
			m_notifiedEndOfTraceDownstream = true;
			m_tempQueue.clear();
			boolean outs;
			try
			{
				outs = onEndOfTrace(m_tempQueue);
			}
			catch (ProcessorException e)
			{
				throw new PushableException(e);
			}
			outputEvent(outs);

			// Notifies the output pushables of the end of the trace
			for (int i = 0; i < m_outputPushables.length; i++)
			{
				Pushable p = m_outputPushables[i];
				if (p == null)
				{
					throw new PushableException("Output " + i
							+ " of this processor is connected to nothing", getProcessor());
				}
				p.notifyEndOfTrace();
			}
		}

		/**
		 * Pushes output event (if any) to the corresponding output {@link Pushable}s.
		 *
		 * @param outs Set to {@code true} to enable the output of an event,
		 * {@code false} otherwise.
		 */
		private final void outputEvent(boolean outs)
		{
			if (!m_tempQueue.isEmpty())
			{
				for (Object[] evt : m_tempQueue)
				{
					if (evt != null)
					{
						for (int i = 0; i < m_outputPushables.length; i++)
						{
							Pushable p = m_outputPushables[i];
							if (p == null)
							{
								throw new PushableException(
										"Output " + i + " of processor " + SynchronousProcessor.this
										+ " is connected to nothing", getProcessor());
							}
							p.push(evt[i]);
						}
					}
				}
				m_tempQueue.clear();
			}
			if (!outs)
			{
				for (int i = 0; i < m_outputPushables.length; i++)
				{
					m_outputPushables[i].notifyEndOfTrace();
				}
			}
		}

		@Override
		public Processor getProcessor()
		{
			return SynchronousProcessor.this;
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
		 * Creates a pullable associated to some of a processor's output traces.
		 * 
		 * @param index
		 *          The index of the trace. Should be between 0 and the processor's
		 *          output arity - 1. This is not checked by the constructor, so beware.
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
				return out_queue.remove();
			}
			return null;
		}

		@Override
		public Object pull()
		{
			if (!hasNext())
			{
				throw new NoSuchElementException();
			}
			Queue<Object> out_queue = m_outputQueues[m_index];
			// If an event is already waiting in the output queue,
			// return it and don't pull anything from the input
			if (!out_queue.isEmpty())
			{
				return out_queue.remove();
			}
			throw new NoSuchElementException();
		}

		@Override
		@SuppressWarnings("squid:S2272") // since() pull throws the exception
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
			for (int tries = 0; tries < Processor.MAX_PULL_RETRIES; tries++)
			{
				for (int i = 0; i < m_inputArity; i++)
				{
					Pullable p = m_inputPullables[i];
					if (p == null)
					{
						throw new PullableException("Input " + i + " of processor " + SynchronousProcessor.this
								+ " is connected to nothing", getProcessor());
					}
					boolean status = p.hasNext();
					if (!status)
					{
						if (allNotifiedEndOfTrace())
						{
							return false;
						}
						Queue<Object[]> last_queue = new ArrayDeque<Object[]>();
						boolean b = onEndOfTrace(last_queue);
						m_hasBeenNotifiedOfEndOfTrace[i] = true;
						if (!b)
						{
							return false;
						}
						for (Object[] front : last_queue)
						{
							for (int j = 0; j < m_outputArity; j++)
							{
								m_outputQueues[j].add(front[j]);
							}
						}
						return true;
					}
				}
				// We are here only if every input pullable has answered YES
				// Pull an event from each
				Object[] inputs = new Object[m_inputArity];
				for (int i = 0; i < m_inputArity; i++)
				{
					Pullable p = m_inputPullables[i];
					// Don't check for p == null, we did it above
					Object o = p.pull();
					inputs[i] = o;
				}
				// Compute output event(s)
				m_tempQueue.clear();
				boolean computed;
				try
				{
					computed = compute(inputs, m_tempQueue);
				}
				catch (ProcessorException e)
				{
					throw new PullableException(e);
				}
				NextStatus status_to_return = NextStatus.NO;
				if (!computed && m_tempQueue.isEmpty())
				{
					// No output will ever be returned: stop there
					return false;
				}
				if (!m_tempQueue.isEmpty())
				{
					// We computed an output event; add it to the output queue
					// and answer YES
					for (Object[] evt : m_tempQueue)
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
							m_tempQueue.clear();
							return false;
						}
					}
					if (status_to_return == NextStatus.YES)
					{
						m_tempQueue.clear();
						return true;
					}
				}
				// Otherwise, try the whole thing again
			}
			m_tempQueue.clear();
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
					if (allNotifiedEndOfTrace())
					{
						return NextStatus.NO;
					}
					Queue<Object[]> last_queue = new ArrayDeque<Object[]>();
					boolean b = onEndOfTrace(last_queue);
					m_hasBeenNotifiedOfEndOfTrace[i] = true;
					if (!b)
					{
						return NextStatus.NO;
					}
					for (Object[] front : last_queue)
					{
						for (int j = 0; j < m_outputArity; j++)
						{
							m_outputQueues[j].add(front[j]);
						}
					}
					return NextStatus.YES;
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
			m_tempQueue.clear();
			boolean computed;
			try
			{
				computed = compute(inputs, m_tempQueue);
			}
			catch (ProcessorException e)
			{
				throw new PullableException(e);
			}
			if (!computed)
			{
				status_to_return = NextStatus.NO;
			}
			else if (!m_tempQueue.isEmpty())
			{
				for (Object[] evt : m_tempQueue)
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
			return SynchronousProcessor.this;
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

		@Override
		public void start()
		{
			// Do nothing
		}

		@Override
		public void stop()
		{
			// Do nothing
		}

		@Override
		public void dispose()
		{
			// Do nothing
		}
	}

	@Override
	public final SynchronousProcessor setEventTracker(EventTracker tracker)
	{
		super.setEventTracker(tracker);
		return this;
	}
}
