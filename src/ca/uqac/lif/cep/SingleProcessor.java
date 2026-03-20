/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2026 Sylvain Hallé

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

import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.util.Equals;
import ca.uqac.lif.cep.util.Lists.MathList;
import ca.uqac.lif.cep.util.Maps.MathMap;
import ca.uqac.lif.petitpoucet.CompositePart;
import ca.uqac.lif.petitpoucet.Duplicable;
import ca.uqac.lif.petitpoucet.Part;
import ca.uqac.lif.petitpoucet.circuit.Node;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Receives zero or more input events, and produces zero or more output events.
 * The processor is the fundamental class where all computation occurs. All of
 * BeepBeep's processors (including yours) are descendants of this class.
 * 
 * A processor is depicted graphically as a "box", with "pipes" representing its
 * input and output streams.
 * <p>
 * <img src="{@docRoot}/doc-files/Processor-generic.png" alt="Processor">
 * <p>
 * This class itself is abstract; nevertheless, it provides important methods
 * for handling input/output event queues, connecting processors together, etc.
 * However, if you write your own processor, you will most likely want to
 * inherit from its child, {@link SynchronousProcessor}, which does some more work
 * for you.
 * <p>
 * The {@link Processor} class does not assume anything about the type of events
 * being input or output. All its input and output queues are therefore declared
 * as containing instances of {@code Object}, Java's most generic type.
 * 
 * @author Sylvain Hallé
 * @since 0.1
 *
 */
public abstract class SingleProcessor extends Node implements Processor, Duplicable, Contextualizable
{
	/**
	 * A string used to identify the program's version
	 */
	public static final transient String s_versionString = "3.13";

	/**
	 * An array of input event queues. This is where the input events will be stored
	 * before the processor consumes them. There are as many input queues as the
	 * input arity of the processor.
	 */
	protected Queue<Object>[] m_inputQueues;

	/**
	 * An array of output event queues. This is where the output events will be
	 * stored when the processor does its computation. There are as many output
	 * queues as the output arity of the processor.
	 */
	protected Queue<Object>[] m_outputQueues;

	/**
	 * A static counter, to be incremented every time a new {@link Processor} is
	 * instantiated. This is used to give a unique integer number to every
	 * processor.
	 */
	private static int s_uniqueIdCounter = 0;

	/**
	 * The unique ID given to this processor instance
	 */
	private final int m_uniqueId;

	/**
	 * The context in which the processor is instantiated
	 */
	protected Context m_context = null;

	/**
	 * Number of times the {@link Pullable#hasNext()} method tries to produce an
	 * output from the input before giving up. While in theory, the method tries "as
	 * long as necessary", in practice a bound was put on the number of attempts as
	 * a safeguard to avoid infinite loops.
	 */
	public static final int MAX_PULL_RETRIES = 10000000;

	/**
	 * Indicates whether the processor has been notified of the end of trace or
	 * not. Each input pushable has its own flag, and the end of trace signal
	 * is propagated only once all upstream processors have sent the
	 * notification.
	 */
	protected boolean[] m_hasBeenNotifiedOfEndOfTrace;

	/**
	 * Indicates whether the processor has notified the end of the trace to the
	 * downstream processors it is connected to. The end of trace signal should
	 * be sent at most once.
	 */
	protected boolean m_notifiedEndOfTraceDownstream;

	/**
	 * Initializes a processor. This has for effect of executing the basic
	 * operations common to every processor:
	 * <ul>
	 * <li>Giving a unique ID</li>
	 * <li>Determining its input and output arity</li>
	 * <li>Creating arrays of empty input and output queues, as well as arrays of
	 * {@link Pullable}s and {@link Pushable}s</li>
	 * </ul>
	 * <p>
	 * If you create your own processor, its constructor <strong>must</strong> start
	 * by calling its ancestor's constructor (which ultimately ends up calling this
	 * constructor). Otherwise, expect a plethora of null pointers and other
	 * oddities.
	 * 
	 * @param in_arity
	 *          The processor's input arity
	 * @param out_arity
	 *          The processor's output arity
	 */
	@SuppressWarnings("unchecked")
	//@ requires in_arity >= 0
	//@ requires out_arity >= 0
	public SingleProcessor(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_uniqueId = s_uniqueIdCounter++;
		m_inputQueues = new Queue[m_ins.length];
		for (int i = 0; i < m_ins.length; i++)
		{
			m_inputQueues[i] = new ArrayDeque<Object>();
		}
		m_outputQueues = new Queue[m_outs.length];
		for (int i = 0; i < m_outs.length; i++)
		{
			m_outputQueues[i] = new ArrayDeque<Object>();
		}
		m_hasBeenNotifiedOfEndOfTrace = new boolean[m_ins.length];
		for (int i = 0; i < m_ins.length; i++)
		{
			m_hasBeenNotifiedOfEndOfTrace[i] = false; 
		}
		m_notifiedEndOfTraceDownstream = false;
	}
	
	@Override
	public void addToInputQueue(int index, Collection<?> c)
	{
		m_inputQueues[index].addAll(c);
	}
	
	@Override
	public void addToOutputQueue(int index, Collection<?> c)
	{
		m_outputQueues[index].addAll(c);
	}

	/**
	 * Determines if all the upstream pushables have sent the end of trace
	 * notification.
	 * @return {@code true} if all notifications have been sent, {@code false}
	 * otherwise
	 */
	protected boolean allNotifiedEndOfTrace()
	{
		for (int i = 0; i < m_ins.length; i++)
		{
			if (!m_hasBeenNotifiedOfEndOfTrace[i])
			{
				return false;
			}
		}
		return true;
	}

	@Override
	public final /*@ null @*/ Object getContext(/*@ non_null @*/ String key)
	{
		if (m_context == null || !m_context.containsKey(key))
		{
			return null;
		}
		return m_context.get(key);
	}

	@Override
	public /*@ non_null @*/ Context getContext()
	{
		// As the context map is created only on demand, we must first
		// check if a map already exists and create it if not
		if (m_context == null)
		{
			m_context = newContext();
		}
		return m_context;
	}

	@Override
	public void setContext(/*@ non_null @*/ String key, Object value)
	{
		// As the context map is created only on demand, we must first
		// check if a map already exists and create it if not
		if (m_context == null)
		{
			m_context = newContext();
		}
		m_context.put(key, value);
	}

	@Override
	public void setContext(/*@ null @*/ Context context)
	{
		// As the context map is created only on demand, we must first
		// check if a map already exists and create it if not
		if (context != null)
		{
			if (m_context == null)
			{
				m_context = newContext();
			}
			m_context.putAll(context);
		}
	}

	/**
	 * Implementation of {@link java.lang.Object#hashCode() hashCode()} specific
	 * to processors. Every processor instance in BeepBeep is given a unique ID;
	 * even a clone of a processor (created using {@link Processor#duplicate()} will
	 * be identical to the original, except for this ID. This behavior cannot be
	 * overridden by descendants.
	 */
	@Override
	public final int hashCode()
	{
		return m_uniqueId;
	}

	/**
	 * Implementation of {@link java.lang.Object#equals(Object) equals()} specific
	 * to processors. Since every processor has a unique ID, equality amounts to
	 * equality of the field {@link #m_uniqueId}. This behavior cannot be
	 * overridden by descendants. 
	 */
	@Override
	public final boolean equals(Object o)
	{
		if (o == null || !(o instanceof Processor))
		{
			return false;
		}
		Processor p = (Processor) o;
		return m_uniqueId == p.getId();
	}

	@Override
	public final int getId()
	{
		return m_uniqueId;
	}
	
  /**
   * Checks that an output part is valid for that processor.
   * @param p The part
   * @throws ExplanationException Thrown if the part is not valid
   */
  protected long checkPart(Part p) throws ExplanationException
  {
  	Part head = CompositePart.head(p);
  	if (!(head instanceof OutputPart))
  	{
  		throw new ExplanationException("Expected an output part");
  	}
  	OutputPart op = (OutputPart) head;
  	if (op.getIndex() < 0 || op.getIndex() >= getOutputArity())
  	{
  		throw new ExplanationException("Output index out of bounds");
  	}
  	Part pos = CompositePart.head(CompositePart.tail(p));
  	if (!(pos instanceof EventAt))
  	{
  		throw new ExplanationException("Expected an event index");
  	}
  	EventAt ea = (EventAt) pos;
  	return ea.getPosition();
  }

	@Override
	public void reset()
	{
		super.reset();
		// Reset input
		for (int i = 0; i < m_ins.length; i++)
		{
			m_inputQueues[i].clear();
		}
		// Reset output
		for (int i = 0; i < m_outs.length; i++)
		{
			m_outputQueues[i].clear();
		}
		for (int i = 0; i < m_ins.length; i++)
		{
			m_hasBeenNotifiedOfEndOfTrace[i] = false; 
		}
		m_notifiedEndOfTraceDownstream = false;
	}

	/**
	 * Checks if all objects in the array are null. This is a convenience method
	 * used by other processor classes (e.g. {@link SynchronousProcessor} to make sure
	 * that some output was generated from a given input
	 * 
	 * @param v
	 *          The array
	 * @return {@code true} if all elements in the array are null,
	 *         {@code false} otherwise
	 */
	public static boolean allNull(Object[] v)
	{
		for (Object o : v)
		{
			if (o != null)
			{
				return false;
			}
		}
		return true;
	}
	
	@Override
	public void evaluate(Object[] inputs, Object[] outputs) throws ProcessorException
	{
		// By default, a processor does not do anything with its input and output
		// queues. It is the responsibility of the descendant classes to implement
		// the logic of consuming input events and producing output events.
	}

	/**
	 * Copies the contents and state of the current processor into another
	 * 
	 * @param p
	 *          The processor to copy contents into
	 */
	public void duplicateInto(SingleProcessor p)
	{
		p.setContext(m_context);
		for (int i = 0; i < m_inputQueues.length; i++)
		{
			p.m_inputQueues[i].addAll(m_inputQueues[i]);
		}
		for (int i = 0; i < m_outputQueues.length; i++)
		{
			p.m_outputQueues[i].addAll(m_outputQueues[i]);
		}
	}

	@Override
	/*@ non_null @*/ public final Set<Class<?>> getInputType(int index)
	{
		Set<Class<?>> classes = new HashSet<Class<?>>();
		if (index >= 0 && index < m_ins.length)
		{
			getInputTypesFor(classes, index);
		}
		return classes;
	}

	/**
	 * Populates the set of classes accepted by the processor for its <i>i</i>-th
	 * input.
	 * <p>
	 * By default, a processor returns the {@link Connector.Variant} type for all
	 * its inputs and all its outputs, meaning that the checking of types in
	 * {@link Connector#connect(Processor...)} will be skipped. A descendant of this
	 * class may choose to define specific types for its input and output, thereby
	 * activating runtime type checking.
	 * 
	 * @param classes
	 *          The set of to fill with classes
	 * @param index
	 *          The index of the input to query
	 */
	public void getInputTypesFor(/*@ non_null @*/ Set<Class<?>> classes, int index)
	{
		classes.add(Variant.class);
	}

	/**
	 * Gets an instance of an empty event queue. It is recommended that processors
	 * call this method to get a queue instance, rather than instantiate their own
	 * manually.
	 * 
	 * @return The queue
	 */
	/*@ non_null @*/ public static Queue<Object[]> getEmptyQueue()
	{
		return new ArrayDeque<Object[]>();
	}
	
	@Override
	public Pullable getPullableInput(int index)
	{
		return (Pullable) m_ins[index];
	}
	
	@Override
	public Pushable getPushableOutput(int index)
	{
		return (Pushable) m_outs[index];
	}
	
	/**
	 * Allows to describe a specific behavior when the trace of input fronts has
	 * reached its end. Called in "push mode" only. In "pull mode", implementing
	 * such a behavior can be done by using {@link Pullable#hasNext()} or
	 * {@link Pullable#hasNextSoft()}.
	 *
	 * @param outputs
	 *          A queue of arrays of objects. The processor should push arrays into
	 *          this queue for every output front it produces. The size of each
	 *          array should be equal to the processor's output arity, although this
	 *          is not enforced.
	 * @return true if the processor should output one or several output fronts,
	 *         false otherwise and by default.
	 * @throws ProcessorException
	 *           An exception thrown when a problem occurs with the operation
	 */
	protected boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException
	{
		return false;
	}
	
	/**
	 * Starts all processors given as an argument
	 * 
	 * @param procs
	 *          The processors
	 */
	public static void startAll(Processor ... procs)
	{
		for (Processor p : procs)
		{
			if (p != null)
			{
				p.start();
			}
		}
	}
	
	/**
	 * Stops all processors given as an argument
	 * 
	 * @param procs
	 *          The processors
	 */
	public static void stopAll(Processor ... procs)
	{
		for (Processor p : procs)
		{
			if (p != null)
			{
				p.stop();
			}
		}
	}

	@Override
	/*@ pure non_null @*/ public final SingleProcessor duplicate()
	{
		return duplicate(false);
	}

	/**
	 * Copies the content of one of the processor's input queue to a collection.
	 * @param index The index of the input queue
	 * @param to The collection where queue contents are copied to
	 * @since 0.11
	 */
	/*@ pure @*/ public void copyInputQueue(int index, Collection<Object> to)
	{
		to.addAll(m_inputQueues[index]);
	}

	/**
	 * Copies the content of one of the processor's output queue to a collection.
	 * @param index The index of the output queue
	 * @param to The collection where queue contents are copied to
	 * @since 0.11
	 */
	/*@ pure @*/ public void copyOutputQueue(int index, Collection<Object> to)
	{
		to.addAll(m_outputQueues[index]);
	}

	@Override
	/*@ non_null @*/ public abstract SingleProcessor duplicate(boolean with_state);

	@Override
	public Queue<Object> getInputQueue(int index)
	{
		Queue<Object> q = new ArrayDeque<Object>();
		q.addAll(m_inputQueues[index]);
		return q;
	}

	@Override
	public Queue<Object> getOutputQueue(int index)
	{
		Queue<Object> q = new ArrayDeque<Object>();
		q.addAll(m_outputQueues[index]);
		return q;
	}

	/**
	 * An object capturing the internal state of a processor,
	 * including the current contents of its input and output queues.
	 * @since 0.10.8
	 */
	public static class InternalProcessorState
	{
		/**
		 * A map between input pipe indices and the contents of the processor's
		 * corresponding input queue.
		 */
		/*@ non_null @*/ protected final MathMap<Integer,MathList<Object>> m_inputQueues;

		/**
		 * A map between output pipe indices and the contents of the processor's
		 * corresponding output queue.
		 */
		/*@ non_null @*/ protected final MathMap<Integer,MathList<Object>> m_outputQueues;

		/**
		 * The internal state of the processor itself.
		 */
		/*@ null @*/ protected Object m_processorState = null;

		public InternalProcessorState(Processor p)
		{
			super();
			m_inputQueues = new MathMap<Integer,MathList<Object>>();
			m_outputQueues = new MathMap<Integer,MathList<Object>>();
			if (p instanceof Stateful)
			{
				m_processorState = ((Stateful) p).getState();
			}
			for (int i = 0; i < p.getInputArity(); i++)
			{
				MathList<Object> q = new MathList<Object>();
				q.addAll(p.getInputQueue(i));
				m_inputQueues.put(i, q);
			}
			for (int i = 0; i < p.getOutputArity(); i++)
			{
				MathList<Object> q = new MathList<Object>();
				q.addAll(p.getOutputQueue(i));
				m_outputQueues.put(i, q);
			}
		}

		@Override
		public boolean equals(Object o)
		{
			if (!(o instanceof InternalProcessorState))
			{
				return false;
			}
			InternalProcessorState ips = (InternalProcessorState) o;
			boolean c1 = Equals.isEqualTo(m_processorState, ips.m_processorState);
			boolean c2 = Equals.isEqualTo(m_inputQueues, ips.m_inputQueues);
			boolean c3 = Equals.isEqualTo(m_outputQueues, ips.m_outputQueues);
			// Three conditions separated to facilitate debugging
			return c1 && c2 && c3;
		}

		@Override
		public String toString()
		{
			StringBuilder out = new StringBuilder();
			out.append("[").append(m_inputQueues).append(",").append(m_outputQueues);
			if (m_processorState != null)
			{
				out.append(",").append(m_processorState);
			}
			out.append("]");
			return out.toString();
		}

		@Override
		public int hashCode()
		{
			int h = 0;
			if (m_processorState != null)
			{
				h += m_processorState.hashCode();
			}
			h += m_inputQueues.hashCode();
			h += m_outputQueues.hashCode();
			return h;
		}
	}
}
