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

import java.util.Collection;
import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.Connector.InputPorts;
import ca.uqac.lif.cep.Connector.OutputPorts;
import ca.uqac.lif.cep.Connector.SelectedInputPipe;
import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.petitpoucet.Connectable;
import ca.uqac.lif.petitpoucet.Duplicable;

public interface Processor extends Contextualizable, Duplicable, Connectable
{
	/**
	 * A string used to identify the program's version
	 */
	public final String s_versionString = "3.14";
	
	/**
	 * Creates a new empty context map.
	 * @return The context map
	 */
	@Override
	public default /*@ non_null @*/ Context newContext()
	{
		return new Context();
	}
	
	/**
	 * Fetches the processor instance's unique ID
	 * 
	 * @return The ID
	 */
	public int getId();

	/**
	 * Resets the processor. This has for effect of flushing the contents of all
	 * input and output event queues. If the processor has an internal state, this
	 * should also reset this state to its "initial" settings (whatever that means
	 * in your context).
	 */
	public void reset();
	
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
	public /*@ non_null @*/ Pushable getPushableInput(int index);

	/**
	 * Returns the {@link Pushable} corresponding to the processor's first input
	 * trace
	 * 
	 * @return The pushable if the processor has at least one input. An
	 *         ArrayIndexOutOfBounds will be thrown if the processor has an input
	 *         arity of 0.
	 */
	public default /*@ non_null @*/ Pushable getPushableInput()
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
	public /*@ non_null @*/ Pullable getPullableOutput(int index);

	/**
	 * Returns the {@link Pullable} corresponding to the processor's first output
	 * trace
	 * 
	 * @return The pullable if the processor has at least one output. An
	 *         ArrayIndexOutOfBounds will be thrown if the processor has an output
	 *         arity of 0.
	 */
	public default /*@ non_null @*/ Pullable getPullableOutput()
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
	public default void setPullableInput(int i, /*@ non_null @*/ Pullable p)
	{
		assignInput(i, p);
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
	public Pullable getPullableInput(int i);
	
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
	public default void setPushableOutput(int i, /*@ non_null @*/ Pushable p)
	{
		assignOutput(i, p);
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
	public /*@ non_null @*/ Pushable getPushableOutput(int i);
	
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
	/*@ non_null @*/ public Set<Class<?>> getInputType(int index);
	
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
	public default Class<?> getOutputType(int index)
	{
		return Variant.class;
	}
	
	@Override
	public default Processor duplicate()
	{
		return duplicate(false);
	}
	
	/**
	 * Starts the processor. This has no effect, except for processors that use
	 * threads; in such a case, calling this method should start the thread.
	 */
	public default void start()
	{
		// Nothing
	}
	
	/**
	 * Stops the processor. This has no effect, except for processors that use
	 * threads; in such a case, calling this method should stop the thread.
	 */
	public default void stop()
	{
		// Nothing
	}
	
	/**
	 * Produces an object that represents the state of the current processor.
	 * A concrete processor should override this method to add whatever state
	 * information that needs to be preserved in the serialization process.
	 * @return Any object representing the processor's state 
	 * (including {@code null})
	 * @since 0.10.2
	 */
	public default Object printState()
	{
		return null;
	}
	
	/**
	 * Reads the state of a processor and uses it to create a new instance
	 * @param o The object containing the processor's state
	 * @return A new processor instance
	 * @since 0.10.2
	 */
	public default Processor readState(Object o)
	{
		throw new UnsupportedOperationException("This processor does not support deserialization");
	}
	
	@Override
	/*@ non_null @*/ public Processor duplicate(boolean with_state);
	
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
	public default Processor or(Processor p)
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
	public default Processor or(CallAfterConnect c)
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
	public default Processor or(SelectedInputPipe p)
	{
		int index = p.getIndex();
		Processor proc = p.getProcessor();
		Connector.connect(this, 0, proc, index);
		return proc;
	}

	/**
   * Groovy helper: allows p.out[i] to designate output i of p.
   */
  public default OutputPorts getOut()
  {
    return new OutputPorts(this);
  }

  /**
   * Groovy helper: allows p.in[i] to designate input i of p.
   */
  public default InputPorts getIn()
  {
    return new InputPorts(this);
  }
  
	/**
	 * Gets the {@link Pushable} corresponding to the processor's first input
	 * pipe. This method is provided to facilitate Groovy's operator overloading,
	 * which maps the construct {@code p >>} to {@code p.rightShift()}.
	 * @return The pushable object
	 */
	public default Pushable rightShift()
	{
		return getPushableInput();
	}
	
	/**
	 * Gets the {@link Pullable} corresponding to the processor's first output
	 * pipe. This method is provided to facilitate Groovy's operator overloading,
	 * which maps the construct {@code p <<} to {@code p.leftShift()}.
	 * @return The pullable object
	 */
	public default Processor leftShift(Object o)
	{
		getPushableInput().push(o);
		return this;
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
	public Queue<Object> getInputQueue(int index);
	
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
	public Queue<Object> getOutputQueue(int index);
	
	void addToInputQueue(int index, Collection<?> c);
	
	void addToOutputQueue(int index, Collection<?> c);
}
