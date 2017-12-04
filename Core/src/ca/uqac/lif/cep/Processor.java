/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.petitpoucet.NodeFunction;

/**
 * Receives zero or more input events, and produces zero or more output
 * events. The processor is the fundamental class where all computation
 * occurs. All of BeepBeep's processors (including yours)
 * are descendants of this class.
 * <p>
 * A processor is depicted graphically as a "box", with "pipes" representing
 * its input and output streams.
 * <p>
 * <img src="{@docRoot}/doc-files/Processor-generic.png" alt="Processor">
 * <p>
 * This class itself is abstract; nevertheless, it provides important
 * methods for handling input/output event queues, connecting processors
 * together, etc. However, if you write your own processor, you will
 * most likely want to inherit from its child, {@link SingleProcessor}, which
 * does some more work for you.
 * <p>
 * The {@link Processor} class does not assume anything about the type of
 * events being input or output. All its input and output queues are
 * therefore declared as containing instances of <code>Object</code>, Java's
 * most generic type.
 * 
 * @author Sylvain Hallé
 * @dictentry
 *
 */
public abstract class Processor implements DuplicableProcessor, Contextualizable
{
	/**
	 * The processor's input arity, i.e. the number of input events it requires
	 * to produce an output
	 */
	protected int m_inputArity;

	/**
	 * The processor's output arity, i.e. the number of output
	 * events it produces
	 */
	protected int m_outputArity;

	/**
	 * A string used to identify the program's version
	 */
	public static final transient String s_versionString = "0.7";

	/**
	 * An array of input event queues. This is where the input events will
	 * be stored before the processor consumes them. There are as many
	 * input queues as the input arity of the processor.
	 */
	protected transient Queue<Object>[] m_inputQueues;

	/**
	 * An object that keeps track of the relationship between input and
	 * output events.
	 */
	protected transient EventTracker m_eventTracker = null;

	/**
	 * An array of output event queues. This is where the output events will
	 * be stored when the processor does its computation. There are as many
	 * output queues as the output arity of the processor.
	 */
	protected transient Queue<Object>[] m_outputQueues;

	/**
	 * An array of {@link Pullable}s, one for each input trace this processor
	 * receives
	 */
	protected transient Pullable[] m_inputPullables;

	/**
	 * An array of {@link Pushable}s, one for each output trace this processor
	 * produces
	 */
	protected transient Pushable[] m_outputPushables;

	/**
	 * A counter incremented upon each input front processed
	 */
	protected int m_inputCount = 0;

	/**
	 * A counter incremented upon each output front processed
	 */
	protected int m_outputCount = 0;

	/**
	 * A static counter, to be incremented every time a new {@link Processor}
	 * is instantiated. This is used to give a unique integer number to
	 * every processor.
	 */
	private static int s_uniqueIdCounter = 0;

	/**
	 * A lock to access the ID counter
	 */
	private static Lock m_counterLock = new ReentrantLock();

	/**
	 * The unique ID given to this processor instance
	 */
	private final int m_uniqueId;

	/**
	 * The context in which the processor is instantiated
	 */
	protected Context m_context = null;

	/**
	 * Number of times the {@link Pullable#hasNext()} method tries to produce
	 * an output from the input before giving up. While in theory, the method
	 * tries "as long as necessary", in practice a bound was put on the
	 * number of attempts as a safeguard to avoid infinite loops.
	 */
	public static final int MAX_PULL_RETRIES = 10000000;

	/**
	 * Initializes a processor. This has for effect of executing the basic
	 * operations common to every processor:
	 * <ul>
	 * <li>Giving a unique ID</li>
	 * <li>Determining its input and output arity</li>
	 * <li>Creating arrays of empty input and output queues, as well as
	 *  arrays of {@link Pullable}s and {@link Pushable}s</li>
	 * </ul>
	 * <p>If you create your own processor, its constructor <strong>must</strong>
	 * start by calling its ancestor's constructor (which ultimately ends up
	 * calling this constructor). Otherwise, expect a plethora of null pointers
	 * and other oddities.
	 * 
	 * @param in_arity The processor's input arity
	 * @param out_arity The processor's output arity
	 */
	@SuppressWarnings("unchecked")
	public Processor(int in_arity, int out_arity)
	{
		super();
		m_inputArity = in_arity;
		m_outputArity = out_arity;
		m_counterLock.lock();
		m_uniqueId = s_uniqueIdCounter++;
		m_counterLock.unlock();
		m_inputQueues = new Queue[m_inputArity];
		for (int i = 0; i < m_inputArity; i++)
		{
			m_inputQueues[i] = new ArrayDeque<Object>();
		}
		m_outputQueues = new Queue[m_outputArity];
		for (int i = 0; i < m_outputArity; i++)
		{
			m_outputQueues[i] = new ArrayDeque<Object>();
		}
		m_inputPullables = new Pullable[m_inputArity];
		m_outputPushables = new Pushable[m_outputArity];
	}

	/**
	 * Creates a new empty context map
	 * @return The context map
	 */
	protected final /*@NotNull*/ Context newContext()
	{
		return new Context();
	}

	/**
	 * Retrieves an object from the processor's context
	 * @param key The key associated to that object
	 * @return The object, or <code>null</code> if no object exists
	 *   with such key
	 */
	public final synchronized /*@Null*/ Object getContext(/*@NotNull*/ String key)
	{
		if (m_context == null || !m_context.containsKey(key))
		{
			return null;
		}
		return m_context.get(key);
	}

	@Override
	public synchronized /*@NotNull*/ Context getContext()
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
	public synchronized void setContext(/*@NotNull*/ String key, Object value)
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
	public synchronized void setContext(/*@Null*/ Context context)
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

	@Override
	public final int hashCode()
	{
		return m_uniqueId;
	}

	@Override
	public final boolean equals(Object o)
	{
		if (o == null || !(o instanceof Processor))
		{
			return false;
		}
		Processor p = (Processor) o;
		return m_uniqueId == p.m_uniqueId;
	}

	/**
	 * Fetches the processor instance's unique ID
	 * @return The ID
	 */
	public int getId()
	{
		return m_uniqueId;
	}

	/**
	 * Resets the processor. This has for effect of flushing the contents
	 * of all input and output event queues. If the processor has an internal
	 * state, this should also reset this state to its "initial" settings
	 * (whatever that means in your context).
	 */
	public void reset()
	{
		// Reset input
		for (int i = 0; i < m_inputArity; i++)
		{
			m_inputQueues[i].clear();
		}
		// Reset output
		for (int i = 0; i < m_outputArity; i++)
		{
			m_outputQueues[i].clear();
		}
	}

	/**
	 * Returns the {@link Pushable} corresponding to the processor's
	 * <i>i</i>-th input trace.
	 * @param index The index. Should be between 0 and the processor's
	 *   input arity - 1 (since indices start at 0).
	 * @return The pushable if the index is within the appropriate range.
	 * Outside of the range, 
	 */
	public abstract /*@NotNull*/ Pushable getPushableInput(int index);

	/**
	 * Returns the {@link Pushable} corresponding to the processor's
	 * first input trace
	 * @return The pushable if the processor has at least one input.
	 * An ArrayIndexOutOfBounds will be thrown
	 * if the processor has an input arity of 0.
	 */
	public final synchronized /*@NotNull*/ Pushable getPushableInput()
	{
		return getPushableInput(0);
	}

	/**
	 * Returns the {@link Pullable} corresponding to the processor's
	 * <i>i</i>-th output trace.
	 * @param index The index. Should be between 0 and the processor's
	 *   output arity - 1 (since indices start at 0).
	 * @return The pullable if the index is within the appropriate range,
	 *   <code>null</code> otherwise.
	 */
	public abstract /*@NotNull*/ Pullable getPullableOutput(int index);

	/**
	 * Returns the {@link Pullable} corresponding to the processor's
	 * first output trace
	 * @return The pullable if the processor has at least one output.
	 * An ArrayIndexOutOfBounds will be thrown
	 * if the processor has an output arity of 0.
	 */
	public final synchronized /*@NotNull*/ Pullable getPullableOutput()
	{
		return getPullableOutput(0);
	}

	/**
	 * Assigns a {@link Pullable} to the processor's <i>i</i>-th input.
	 * @param i The index of the input. An ArrayIndexOutOfBounds will be thrown
	 * if it is out of range.
	 * @param p The pullable to assign it to
	 */
	public synchronized void setPullableInput(int i, /*@NotNull*/ Pullable p)
	{
		m_inputPullables[i] = p;
	}

	/**
	 * Returns the {@link Pullable} corresponding to the processor's
	 * <i>i</i>-th input
	 * @param i The index of the input. Should be greater than 0
	 *   and less than the processor's output arity.
	 *   Outside these bounds, an ArrayIndexOutOfBounds will be thrown.
	 * @return The pullable
	 */
	public synchronized Pullable getPullableInput(int i)
	{
		return m_inputPullables[i];
	}

	/**
	 * Assigns a {@link Pushable} to the processor's <i>i</i>-th output.
	 * @param i The index of the output. Should be greater than 0
	 *   and less than the processor's output arity.
	 *   Outside these bounds, an ArrayIndexOutOfBounds will be thrown.
	 * @param p The pushable to assign it to
	 */
	public synchronized void setPushableOutput(int i, /*@NotNull*/ Pushable p)
	{
		m_outputPushables[i] = p;
	}

	/**
	 * Retrieves the {@link Pushable} associated to the processor's
	 * <i>i</i>-th output.
	 * @param i The index of the output. Should be greater than 0
	 *   (not checked) and less than the processor's output arity.
	 *   Outside these bounds, an ArrayIndexOutOfBounds will be thrown.
	 * @param p The pushable to assign it to
	 * @return The pushable
	 */
	public synchronized /*@NotNull*/ Pushable getPushableOutput(int i)
	{
		return m_outputPushables[i];
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

	/**
	 * Checks if all objects in the array are null. This is a convenience
	 * method used by other processor classes (e.g. {@link SingleProcessor}
	 * to make sure that some output was generated from a given input
	 * @param v The array
	 * @return <code>true</code> if all elements in the
	 *   array are null, <code>false</code> otherwise
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

	/**
	 * Copies the contents and state of the current processor into another
	 * @param p The processor to copy contents into
	 */
	public void cloneInto(Processor p)
	{
		p.m_eventTracker = m_eventTracker;
		p.setContext(m_context);
	}

	/**
	 * Gets the type of events the processor accepts for its <i>i</i>-th
	 * input trace. Note that this method returns a <em>set</em>, in the case
	 * where the processor accepts various types of objects (for example,
	 * a processor accepting <code>Number</code>s, but also <code>String</code>s
	 * it converts into numbers internally).
	 * @param index The index of the input to query
	 * @return A set of classes. If <code>index</code> it less than 0 or
	 *   greater than the processor's declared input arity, the set will
	 *   be empty.
	 */
	public final /*@NotNull*/ Set<Class<?>> getInputType(int index)
	{
		Set<Class<?>> classes = new HashSet<Class<?>>();
		if (index >= 0 && index < m_inputArity)
		{
			getInputTypesFor(classes, index);
		}
		return classes;
	}

	/**
	 * Populates the set of classes accepted by the processor for its
	 * <i>i</i>-th input.
	 * <p>
	 * By default, a processor returns the {@link Connector.Variant} type
	 * for all its inputs and all its outputs, meaning that the checking of
	 * types in {@link Connector#connect(Processor...)} will be skipped.
	 * A descendant of this class may choose to define specific types for
	 * its input and output, thereby activating runtime type checking.
	 * @param classes The set of to fill with classes
	 * @param index The index of the input to query
	 */
	public void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
	{
		classes.add(Variant.class);
	}

	/**
	 * Returns the type of the events produced by the processor for its
	 * <i>i</i>-th output.
	 * <p>
	 * By default, a processor returns the {@link Connector.Variant} type
	 * for all its inputs and all its outputs, meaning that the checking of
	 * types in {@link Connector#connect(Processor...)} will be skipped.
	 * A descendant of this class may choose to define specific types for
	 * its input and output, thereby activating runtime type checking.
	 * @param index The index of the output to query
	 * @return The type of the output. If <code>index</code> it less than 0 or
	 *   greater than the processor's declared output arity, this method
	 *   <em>may</em> throw an IndexOutOfBoundsException.
	 */
	public Class<?> getOutputType(int index)
	{
		return Variant.class;
	}

	/**
	 * Gets an instance of an empty event queue. It is recommended that
	 * processors call this method to get a queue instance, rather than
	 * instantiate their own manually.
	 * @return The queue
	 */
	public static Queue<Object[]> getEmptyQueue()
	{
		return new ArrayDeque<Object[]>();
	}

	/**
	 * Starts the processor. This has no effect, except for processors
	 * that use threads; in such a case, calling this method should
	 * start the thread.
	 */
	public void start()
	{
		// Nothing
	}

	/**
	 * Stops the processor. This has no effect, except for processors
	 * that use threads; in such a case, calling this method should
	 * stop the thread.
	 */
	public void stop()
	{
		// Nothing
	}

	/**
	 * Starts all processors given as an argument
	 * @param procs The processors
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
	 * @param procs The processors
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

	/**
	 * Gets the instance of event tracker associated to this processor
	 * @return The event tracker, or {@code null} of no event tracker is
	 * associated to this processor
	 */
	public final /*@Null*/ EventTracker getEventTracker()
	{
		return m_eventTracker;
	}

	/**
	 * Associates an event tracker to this processor
	 * @param tracker The event tracker, or {@code null} to remove the
	 * association to an existing tracker
	 * @return This processor
	 */
	public final Processor setEventTracker(/*@Null*/ EventTracker tracker)
	{
		m_eventTracker = tracker;
		return this;
	}

	public void associateToInput(int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos)
	{
		if (m_eventTracker != null)
		{
			m_eventTracker.associateToInput(m_uniqueId, in_stream_index, in_stream_pos, out_stream_index, out_stream_pos);
		}
	}

	public void associateTo(NodeFunction f, int out_stream_index, int out_stream_pos)
	{
		if (m_eventTracker != null)
		{
			m_eventTracker.associateTo(m_uniqueId, f, out_stream_index, out_stream_pos);
		}
	}

	public void associateToOutput(int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos)
	{
		if (m_eventTracker != null)
		{
			m_eventTracker.associateToOutput(m_uniqueId, in_stream_index, in_stream_pos, out_stream_index, out_stream_pos);
		}
	}
}
