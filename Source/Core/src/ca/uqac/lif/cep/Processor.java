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

import java.util.ArrayDeque;
import java.util.Queue;

/**
 * Receives zero or more input events, and produces zero or more output
 * events. The processor is the fundamental class where all computation
 * occurs. All of BeepBeep's processors (including yours)
 * are descendants of this class.
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
 *
 */
public abstract class Processor
{
	/**
	 * The processor's input arity, i.e. the number of input events it requires
	 * to produce an output
	 */
	protected final int m_inputArity;

	/**
	 * The processor's output arity, i.e. the number of output
	 * events it produces
	 */
	protected int m_outputArity;

	/**
	 * An array of input event queues. This is where the input events will
	 * be stored before the processor consumes them. There are as many
	 * input queues as the input arity of the processor.
	 */
	protected final Queue<Object>[] m_inputQueues;

	/**
	 * An array of output event queues. This is where the output events will
	 * be stored when the processor does its computation. There are as many
	 * output queues as the output arity of the processor.
	 */
	protected Queue<Object>[] m_outputQueues;

	/**
	 * An array of {@link Pullable}s, one for each input trace this processor
	 * receives
	 */
	protected Pullable[] m_inputPullables;

	/**
	 * An array of {@link Pushable}s, one for each output trace this processor
	 * produces
	 */
	protected Pushable[] m_outputPushables;

	/**
	 * A static counter, to be incremented every time a new {@link Processor}
	 * is instantiated. This is used to give a unique integer number to
	 * every processor.
	 */
	protected static int s_uniqueIdCounter = 0;

	/**
	 * The unique ID given to this processor instance 
	 */
	protected int m_uniqueId;

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
	}

	@Override
	public int hashCode()
	{
		return m_uniqueId;
	}

	@Override
	public boolean equals(Object o)
	{
		if (!(o instanceof Processor))
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
	public abstract void reset();

	/**
	 * Returns the {@link Pushable} corresponding to the processor's
	 * <i>i</i>-th input trace. 
	 * @param index The index. Should be between 0 and the processor's
	 *   input arity - 1 (since indices start at 0).
	 * @return The pushable if the index is within the appropriate range,
	 *   <code>null</code> otherwise.
	 */
	public abstract Pushable getPushableInput(int index);

	/**
	 * Returns the {@link Pullable} corresponding to the processor's
	 * <i>i</i>-th output trace. 
	 * @param index The index. Should be between 0 and the processor's
	 *   output arity - 1 (since indices start at 0).
	 * @return The pullable if the index is within the appropriate range,
	 *   <code>null</code> otherwise.
	 */
	public abstract Pullable getPullableOutput(int index);

	/**
	 * Assigns a {@link Pullable} to the processor's <i>i</i>-th input.
	 * @param i The index of the input
	 * @param p The pullable to assignt it to
	 */
	public void setPullableInput(int i, Pullable p)
	{
		if (i < m_inputPullables.length)
		{
			m_inputPullables[i] = p;
		}
	}

	/**
	 * Assigns a {@link Pushable} to the processor's <i>i</i>-th output.
	 * @param i The index of the output. Should be greater than 0
	 *   (not checked) and less than the processor's output arity.
	 *   Outside these bounds, nothing will occur.
	 * @param p The pushable to assign it to
	 */
	public void setPushableOutput(int i, Pushable p)
	{
		if (i < m_outputPushables.length)
		{
			m_outputPushables[i] = p;
		}
	}

	/**
	 * Retrieves the {@link Pushable} associated to the processor's 
	 * <i>i</i>-th output.
	 * @param i The index of the output. Should be greater than 0
	 *   (not checked) and less than the processor's output arity.
	 *   Outside these bounds, nothing will occur.
	 * @return The pushable, <code>null</code> if <code>i</code> is
	 *   out of range
	 */	
	public Pushable getPushableOutput(int i)
	{
		if (i < m_outputPushables.length)
		{
			return m_outputPushables[i];
		}
		return null;
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
	 * Extracts a processor out of the object passed as an argument. A
	 * instance of Processor will be returned as is, while other objects
	 * will be wrapped into a constant processor returning that object.
	 * @param o The input object
	 * @return A processor
	 */
	public static Processor liftProcessor(Object o)
	{
		if (o instanceof Processor)
		{
			return (Processor) o;
		}
		return new Constant(o);
	}
}
