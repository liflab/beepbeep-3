/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2024 Sylvain Hallé

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

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.cep.Connector.PipeSelector;
import ca.uqac.lif.cep.Connector.SelectedInputPipe;
import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.util.Equals;
import ca.uqac.lif.cep.util.Lists.MathList;
import ca.uqac.lif.cep.util.Maps.MathMap;
import ca.uqac.lif.petitpoucet.NodeFunction;
import ca.uqac.lif.petitpoucet.ProvenanceNode;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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
public abstract class Processor implements DuplicableProcessor, 
Contextualizable, Printable, Readable
{
	/**
	 * The processor's input arity, i.e. the number of input events it requires to
	 * produce an output
	 */
	protected int m_inputArity;

	/**
	 * The processor's output arity, i.e. the number of output events it produces
	 */
	protected int m_outputArity;

	/**
	 * A string used to identify the program's version
	 */
	public static final transient String s_versionString = "0.11.2";

	/**
	 * An array of input event queues. This is where the input events will be stored
	 * before the processor consumes them. There are as many input queues as the
	 * input arity of the processor.
	 */
	protected transient Queue<Object>[] m_inputQueues;

	/**
	 * An object that keeps track of the relationship between input and output
	 * events.
	 */
	protected transient EventTracker m_eventTracker = null;

	/**
	 * An array of output event queues. This is where the output events will be
	 * stored when the processor does its computation. There are as many output
	 * queues as the output arity of the processor.
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
	public static final transient int MAX_PULL_RETRIES = 10000000;

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
	public Processor(int in_arity, int out_arity)
	{
		super();
		m_inputArity = in_arity;
		m_outputArity = out_arity;
		m_uniqueId = s_uniqueIdCounter++;
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
		m_hasBeenNotifiedOfEndOfTrace = new boolean[m_inputArity];
		for (int i = 0; i < m_inputArity; i++)
		{
			m_hasBeenNotifiedOfEndOfTrace[i] = false; 
		}
		m_notifiedEndOfTraceDownstream = false;
	}

	/**
	 * Determines if all the upstream pushables have sent the end of trace
	 * notification.
	 * @return {@code true} if all notifications have been sent, {@code false}
	 * otherwise
	 */
	protected boolean allNotifiedEndOfTrace()
	{
		for (int i = 0; i < m_inputArity; i++)
		{
			if (!m_hasBeenNotifiedOfEndOfTrace[i])
			{
				return false;
			}
		}
		return true;
	}

	/**
	 * Creates a new empty context map
	 * 
	 * @return The context map
	 */
	protected final /*@ non_null @*/ Context newContext()
	{
		return new Context();
	}

	/**
	 * Retrieves an object from the processor's context
	 * 
	 * @param key
	 *          The key associated to that object
	 * @return The object, or {@code null} if no object exists with such key
	 */
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
		return m_uniqueId == p.m_uniqueId;
	}

	/**
	 * Fetches the processor instance's unique ID
	 * 
	 * @return The ID
	 */
	public final int getId()
	{
		return m_uniqueId;
	}

	/**
	 * Resets the processor. This has for effect of flushing the contents of all
	 * input and output event queues. If the processor has an internal state, this
	 * should also reset this state to its "initial" settings (whatever that means
	 * in your context).
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
		for (int i = 0; i < m_inputArity; i++)
		{
			m_hasBeenNotifiedOfEndOfTrace[i] = false; 
		}
		m_notifiedEndOfTraceDownstream = false;
		m_inputCount = 0;
		m_outputCount = 0;
	}

	/**
	 * Returns the {@link Pushable} corresponding to the processor's <i>i</i>-th
	 * input trace.
	 * 
	 * @param index
	 *          The index. Should be between 0 and the processor's input arity - 1
	 *          (since indices start at 0).
	 * @return The pushable if the index is within the appropriate range. Outside of
	 *         the range,
	 */
	/*@ assume index >= 0 @*/
	public abstract /*@ non_null @*/ Pushable getPushableInput(int index);

	/**
	 * Returns the {@link Pushable} corresponding to the processor's first input
	 * trace
	 * 
	 * @return The pushable if the processor has at least one input. An
	 *         ArrayIndexOutOfBounds will be thrown if the processor has an input
	 *         arity of 0.
	 */
	public final /*@ non_null @*/ Pushable getPushableInput()
	{
		return getPushableInput(0);
	}

	/**
	 * Returns the {@link Pullable} corresponding to the processor's <i>i</i>-th
	 * output trace.
	 * 
	 * @param index
	 *          The index. Should be between 0 and the processor's output arity - 1
	 *          (since indices start at 0).
	 * @return The pullable if the index is within the appropriate range,
	 *         {@code null} otherwise.
	 */
	public abstract /*@ non_null @*/ Pullable getPullableOutput(int index);

	/**
	 * Returns the {@link Pullable} corresponding to the processor's first output
	 * trace
	 * 
	 * @return The pullable if the processor has at least one output. An
	 *         ArrayIndexOutOfBounds will be thrown if the processor has an output
	 *         arity of 0.
	 */
	public final /*@ non_null @*/ Pullable getPullableOutput()
	{
		return getPullableOutput(0);
	}

	/**
	 * Assigns a {@link Pullable} to the processor's <i>i</i>-th input.
	 * 
	 * @param i
	 *          The index of the input. An ArrayIndexOutOfBounds will be thrown if
	 *          it is out of range.
	 * @param p
	 *          The pullable to assign it to
	 */
	public void setPullableInput(int i, /*@ non_null @*/ Pullable p)
	{
		m_inputPullables[i] = p;
	}

	/**
	 * Returns the {@link Pullable} corresponding to the processor's <i>i</i>-th
	 * input
	 * 
	 * @param i
	 *          The index of the input. Should be greater than 0 and less than the
	 *          processor's output arity. Outside these bounds, an
	 *          ArrayIndexOutOfBounds will be thrown.
	 * @return The pullable
	 */
	public Pullable getPullableInput(int i)
	{
		return m_inputPullables[i];
	}

	/**
	 * Assigns a {@link Pushable} to the processor's <i>i</i>-th output.
	 * 
	 * @param i
	 *          The index of the output. Should be greater than 0 and less than the
	 *          processor's output arity. Outside these bounds, an
	 *          ArrayIndexOutOfBounds will be thrown.
	 * @param p
	 *          The pushable to assign it to
	 */
	public void setPushableOutput(int i, /*@ non_null @*/ Pushable p)
	{
		m_outputPushables[i] = p;
	}

	/**
	 * Retrieves the {@link Pushable} associated to the processor's <i>i</i>-th
	 * output.
	 * 
	 * @param i
	 *          The index of the output. Should be greater than 0 (not checked) and
	 *          less than the processor's output arity. Outside these bounds, an
	 *          ArrayIndexOutOfBounds will be thrown.
	 * @return The pushable
	 */
	public /*@ non_null @*/ Pushable getPushableOutput(int i)
	{
		return m_outputPushables[i];
	}

	/**
	 * Returns the processor's input arity
	 * 
	 * @return The arity
	 */
	/*@ pure @*/ public final int getInputArity()
	{
		return m_inputArity;
	}

	/**
	 * Returns the processor's output arity
	 * 
	 * @return The arity
	 */
	/*@ pure @*/ public final int getOutputArity()
	{
		return m_outputArity;
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

	/**
	 * Copies the contents and state of the current processor into another
	 * 
	 * @param p
	 *          The processor to copy contents into
	 */
	public void duplicateInto(Processor p)
	{
		p.m_eventTracker = m_eventTracker;
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

	/**
	 * Gets the type of events the processor accepts for its <i>i</i>-th input
	 * trace. Note that this method returns a <em>set</em>, in the case where the
	 * processor accepts various types of objects (for example, a processor
	 * accepting {@code Number}s, but also {@code String}s it converts
	 * into numbers internally).
	 * 
	 * @param index
	 *          The index of the input to query
	 * @return A set of classes. If {@code index} is less than 0 or greater
	 *         than the processor's declared input arity, the set will be empty.
	 */
	//@ requires index >= 0
	/*@ non_null @*/ public final Set<Class<?>> getInputType(int index)
	{
		Set<Class<?>> classes = new HashSet<Class<?>>();
		if (index >= 0 && index < m_inputArity)
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
	 * Returns the type of the events produced by the processor for its <i>i</i>-th
	 * output.
	 * <p>
	 * By default, a processor returns the {@link Connector.Variant} type for all
	 * its inputs and all its outputs, meaning that the checking of types in
	 * {@link Connector#connect(Processor...)} will be skipped. A descendant of this
	 * class may choose to define specific types for its input and output, thereby
	 * activating runtime type checking.
	 * 
	 * @param index
	 *          The index of the output to query
	 * @return The type of the output. If {@code index} it less than 0 or
	 *         greater than the processor's declared output arity, this method
	 *         <em>may</em> throw an IndexOutOfBoundsException.
	 */
	// requires index >= 0 && index < getInputArity()
	public Class<?> getOutputType(int index)
	{
		return Variant.class;
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

	/**
	 * Starts the processor. This has no effect, except for processors that use
	 * threads; in such a case, calling this method should start the thread.
	 */
	public void start()
	{
		// Nothing
	}

	/**
	 * Stops the processor. This has no effect, except for processors that use
	 * threads; in such a case, calling this method should stop the thread.
	 */
	public void stop()
	{
		// Nothing
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

	/**
	 * Gets the instance of event tracker associated to this processor
	 * 
	 * @return The event tracker, or {@code null} of no event tracker is associated
	 *         to this processor
	 */
	public final /*@ null @*/ EventTracker getEventTracker()
	{
		return m_eventTracker;
	}

	/**
	 * Associates an event tracker to this processor
	 * 
	 * @param tracker
	 *          The event tracker, or {@code null} to remove the association to an
	 *          existing tracker
	 * @return This processor
	 */
	public Processor setEventTracker(/*@ null @*/ EventTracker tracker)
	{
		m_eventTracker = tracker;
		return this;
	}

	/**
	 * Associates an input event to an output event.
	 * @param in_stream_index The index of the processor's input stream 
	 * @param in_stream_pos The position of the event in the input stream
	 * @param out_stream_index The index of the processor's output stream 
	 * @param out_stream_pos The position of the event in the output stream
	 */
	public void associateToInput(int in_stream_index, int in_stream_pos, int out_stream_index,
			int out_stream_pos)
	{
		if (m_eventTracker != null)
		{
			m_eventTracker.associateToInput(m_uniqueId, in_stream_index, in_stream_pos, out_stream_index,
					out_stream_pos);
		}
	}

	/**
	 * Associates a node function to a particular event of processor's
	 * output stream. 
	 * @param f The node function
	 * @param out_stream_index The index of the processor's output stream 
	 * @param out_stream_pos The position of the event in the output stream
	 */
	public void associateTo(NodeFunction f, int out_stream_index, int out_stream_pos)
	{
		if (m_eventTracker != null)
		{
			m_eventTracker.associateTo(m_uniqueId, f, out_stream_index, out_stream_pos);
		}
	}

	/**
	 * Associates an input event to an output event.
	 * @param in_stream_index The index of the processor's input stream 
	 * @param in_stream_pos The position of the event in the input stream
	 * @param out_stream_index The index of the processor's output stream 
	 * @param out_stream_pos The position of the event in the output stream
	 */
	public void associateToOutput(int in_stream_index, int in_stream_pos, int out_stream_index,
			int out_stream_pos)
	{
		if (m_eventTracker != null)
		{
			m_eventTracker.associateToOutput(m_uniqueId, in_stream_index, in_stream_pos, out_stream_index,
					out_stream_pos);
		}
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
	 * Gets the number of event fronts received so far by this processor
	 * @return The number of fronts
	 */
	public final int getInputCount()
	{
		return m_inputCount;
	}

	/**
	 * Gets the number of event fronts produced so far by this processor
	 * @return The number of fronts
	 */
	public final int getOutputCount()
	{
		return m_outputCount;
	}

	/**
	 * Prints the contents of this processor into an object printer.
	 * @param printer The printer to print this processor to
	 * @return The printed processor
	 * @since 0.10.2
	 */
	@Override
	public final Object print(ObjectPrinter<?> printer) throws ProcessorException
	{
		Map<String,Object> contents = new HashMap<String,Object>();
		contents.put("id", m_uniqueId);
		contents.put("input-count", m_inputCount);
		contents.put("output-count", m_outputCount);
		contents.put("context", m_context);
		List<Queue<Object>> in_queues = new ArrayList<Queue<Object>>(m_inputQueues.length);
		for (Queue<Object> q : m_inputQueues)
		{
			in_queues.add(q);
		}
		contents.put("input-queues", in_queues);
		List<Queue<Object>> out_queues = new ArrayList<Queue<Object>>(m_outputQueues.length);
		for (Queue<Object> q : m_outputQueues)
		{
			out_queues.add(q);
		}
		contents.put("output-queues", out_queues);
		contents.put("contents", printState());
		try
		{
			return printer.print(contents);
		}
		catch (PrintException e)
		{
			throw new ProcessorException(e);
		}
	}

	/**
	 * Produces an object that represents the state of the current processor.
	 * A concrete processor should override this method to add whatever state
	 * information that needs to be preserved in the serialization process.
	 * @return Any object representing the processor's state 
	 * (including {@code null})
	 * @since 0.10.2
	 */
	protected Object printState()
	{
		return null;
	}

	/**
	 * Reads the content of a processor from a serialized object.
	 * @param reader An object reader
	 * @param o The object to read from
	 * @return The serialized processor
	 * @throws ProcessorException If the read operation failed for some reason
	 */
	@SuppressWarnings("unchecked")
	@Override
	public final Processor read(ObjectReader<?> reader, Object o) throws ProcessorException
	{
		Map<String, Object> contents = null;
		try
		{
			contents = (Map<String,Object>) reader.read(o);
		}
		catch (ReadException e)
		{
			throw new ProcessorException(e);
		}
		Processor p = null;
		if (contents.containsKey("contents"))
		{
			Object o_contents = contents.get("contents");
			try
			{
				p = readState(o_contents);
			}
			catch (UnsupportedOperationException e)
			{
				throw new ProcessorException(e);
			}
		}
		if (p == null)
		{
			throw new ProcessorException("The processor returned null with being deserialized");
		}
		p.m_inputCount = ((Number) contents.get("input-count")).intValue();
		p.m_outputCount = ((Number) contents.get("output-count")).intValue();
		try
		{
			reader.setField(p, "m_uniqueId", ((Number) contents.get("id")).intValue());
		}
		catch (ReadException e)
		{
			throw new ProcessorException(e);
		}
		List<Queue<Object>> in_queues = (List<Queue<Object>>) contents.get("input-queues");
		for (int i = 0; i < in_queues.size(); i++)
		{
			p.m_inputQueues[i] = in_queues.get(i);
		}
		List<Queue<Object>> out_queues = (List<Queue<Object>>) contents.get("output-queues");
		for (int i = 0; i < out_queues.size(); i++)
		{
			p.m_outputQueues[i] = in_queues.get(i);
		}
		return p;
	}

	/**
	 * Reads the state of a processor and uses it to create a new instance
	 * @param o The object containing the processor's state
	 * @return A new processor instance
	 * @since 0.10.2
	 */
	protected Processor readState(Object o)
	{
		throw new UnsupportedOperationException("This processor does not support deserialization");
	}

	@Override
	/*@ pure non_null @*/ public final Processor duplicate()
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
	/*@ non_null @*/ public abstract Processor duplicate(boolean with_state);

	/**
	 * Gets the leaves of a provenance tree
	 * @param root The root of the tree
	 * @return A list of nodes that correspond to the leaves
	 */
	public static List<ProvenanceNode> getLeaves(ProvenanceNode root)
	{
		List<ProvenanceNode> leaves = new ArrayList<ProvenanceNode>();
		getLeaves(root, leaves);
		return leaves;
	}

	/**
	 * Accumulates the leaves of a provenance tree in a list
	 * @param root The current node in the tree
	 * @param leaves The list of leaves
	 */
	protected static void getLeaves(ProvenanceNode root, List<ProvenanceNode> leaves)
	{
		if (root == null)
		{
			return;
		}
		List<ProvenanceNode> children = root.getChildren();
		if (children.isEmpty())
		{
			leaves.add(root);
		}
		else
		{
			for (ProvenanceNode child : children)
			{
				getLeaves(child, leaves);
			}
		}
	}

	/**
	 * Connects the first output pipe of this processor to the first input pipe
	 * of another processor.
	 * <p>
	 * Java programmers probably won't use this method, but users of the Groovy
	 * language can benefit from its operator overloading conventions, which map
	 * the construct {@code p | q} to {@code p.or(q)}. This can be used to
	 * easily pipe two processors together:
	 * <pre>{@code 
	 * def p = (some processor)
	 * def q = (some other processor)
	 * p | q // Connects p to q
	 * }</pre>
	 * @param p The other processor
	 * @return The other processor
	 * @since 0.10.9
	 */
	public Processor or(Processor p)
	{
		Connector.connect(this, p);
		return p;
	}
	
	/**
	 * Operates similar to {@link #or(Processor)}, but also calls a method
	 * after the connection has been established. Currently there is a single use
	 * for this method, which is when {@link GroupProcessor#or(Processor)} is
	 * called &mdash;which, again, typically only occurs in the context of a
	 * Groovy script.
	 * @param c The object that contains the method to call
	 * @return The processor encapsulated in {@code c}
	 * @since 0.11.4
	 */
	public Processor or(CallAfterConnect c)
	{
		Processor p = c.getProcessor();
		Connector.connect(this, p);
		c.call();
		return p;
	}

	/**
	 * Connects the output at index 0 of the current processor to the input
	 * of another processor.
	 * <p>
	 * Java programmers probably won't use this method. However, combined with
	 * the definition of {@link #getAt(int)}, users of the Groovy language
	 * can benefit from its operator overloading conventions, which map
	 * the construct {@code p | q} to {@code p.or(q)}. This can be used to
	 * easily pipe two processors together:
	 * <pre>{@code 
	 * def p = (some processor)
	 * def q = (some other processor)
	 * p | q[1] // Connects p to pipe index 1 of q
	 * }</pre>
	 * The above example works because {@code q[1]} returns {@code q}'s
	 * input pushable for pipe index 1.
	 * @param p The pushable object representing the input of the other processor
	 * to which the current output should be connected.
	 * @return The other processor
	 * @since 0.10.9
	 */
	public Processor or(SelectedInputPipe p)
	{
		int index = p.getIndex();
		Processor proc = p.getProcessor();
		Connector.connect(this, 0, proc, index);
		return proc;
	}

	/**
	 * Gets the {@link PipeSelector} object corresponding to the processor's
	 * input or output pipe for a given index.
	 * <p>
	 * Java programmers probably won't use this method, but users of the Groovy
	 * language can benefit from its operator overloading conventions, which map
	 * the construct {@code p[x]} to {@code p.getAt(x)}. Combined with the
	 * definition of {@link #or(Connector.SelectedInputPipe)}, this can be used
	 * to easily pipe two processors together:
	 * <pre>{@code 
	 * def p = (some processor)
	 * def q = (some other processor)
	 * p | q[1] // Connects p to pipe index 1 of q
	 * }</pre>
	 * @param index The input pipe index
	 * @return The pushable object
	 * @since 0.11
	 */
	/*@ pure non_null @*/ public PipeSelector getAt(int index)
	{
		return new PipeSelector(this, index);
	}

	public Pushable rightShift(int index)
	{
		return getPushableInput(index);
	}

	public Pullable leftShift(int index)
	{
		return getPullableInput(index);
	}

	/**
	 * Gets the content of the processor's input queue at a given index. Note
	 * that the method returns a <em>copy</em> of the queue, and not its own
	 * internal queue. This means that modifications to the returned queue have
	 * no effect on the processor's internal state.
	 * 
	 * @param index The index of the input
	 * @return The contents of the queue
	 * @since 0.11.2
	 */
	public Queue<Object> getInputQueue(int index)
	{
		Queue<Object> q = new ArrayDeque<Object>();
		q.addAll(m_inputQueues[index]);
		return q;
	}

	/**
	 * Gets the content of the processor's output queue at a given index. Note
	 * that the method returns a <em>copy</em> of the queue, and not its own
	 * internal queue. This means that modifications to the returned queue have
	 * no effect on the processor's internal state.
	 * 
	 * @param index The index of the input
	 * @return The contents of the queue
	 * @since 0.11.2
	 */
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
				p.copyInputQueue(i, q);
				m_inputQueues.put(i, q);
			}
			for (int i = 0; i < p.getOutputArity(); i++)
			{
				MathList<Object> q = new MathList<Object>();
				p.copyOutputQueue(i, q);
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
