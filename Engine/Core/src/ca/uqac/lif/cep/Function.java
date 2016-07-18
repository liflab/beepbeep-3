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

import java.util.Map;
import java.util.Set;

/**
 * Represents a stateless <i>m</i>-to-<i>n</i> function.
 * 
 * @author Sylvain Hallé
 */
public abstract class Function implements Cloneable
{
	/**
	 * The maximum input arity that a function can have
	 */
	public static int s_maxInputArity = 10;

	/**
	 * Evaluates the outputs of the function, given some inputs
	 * @param inputs The arguments of the function. The size of the array
	 *   should be equal to the function's declared input arity.
	 * @param context The context in which the evaluation is done. If the
	 *   function's arguments contains placeholders, they will be replaced
	 *   by the corresponding object fetched from this map before
	 *   calling {@link #compute(Object[])}
	 * @return The outputs of the function. The size of the array returned
	 *   should be equal to the function's declared output arity.
	 */
	public final Object[] evaluate(Object[] inputs, Map<String,Object> context)
	{
		// If no context is given, call compute() straight away
		if (context == null)
		{
			return compute(inputs);
		}
		Object[] concrete_inputs = new Object[inputs.length];
		// Check each of the concrete inputs if it is a placeholder
		for (int i = 0; i < inputs.length; i++)
		{
			Object argument = inputs[i];
			if (argument instanceof ArgumentPlaceholder)
			{
				// If so, fetch concrete object in context
				ArgumentPlaceholder ap = (ArgumentPlaceholder) argument;
				String ap_name = ap.getName();
				if (context.containsKey(ap_name))
				{
					concrete_inputs[i] = context.get(ap_name);
				}
				else
				{
					// If we didn't find the value in the context, leave the argument
					// as is and hope the function will know what to do with it
					concrete_inputs[i] = argument;
				}
			}
			else
			{
				concrete_inputs[i] = argument;
			}
		}
		// Call compute() with concrete inputs
		return compute(concrete_inputs);
	}

	/**
	 * Evaluates the outputs of the function, given some inputs
	 * @param inputs The arguments of the function. The size of the array
	 *   should be equal to the function's declared input arity.
	 * @return The outputs of the function. The size of the array returned
	 *   should be equal to the function's declared output arity.
	 */
	public final Object[] evaluate(Object[] inputs)
	{
		return compute(inputs);
	}
	
	/**
	 * Computes the outputs of the function, given some inputs
	 * @param inputs The arguments of the function. The size of the array
	 *   should be equal to the function's declared input arity.
	 * @return The outputs of the function. The size of the array returned
	 *   should be equal to the function's declared output arity.
	 */
	public abstract Object[] compute(Object[] inputs);
	
	/**
	 * Gets the function's input arity, i.e. the number of arguments
	 * it takes.
	 * @return The input arity
	 */
	public abstract int getInputArity();
	
	/**
	 * Gets the function's output arity, i.e. the number of elements
	 * it outputs. (We expect that most functions will have an output
	 * arity of 1.)
	 * @return The output arity
	 */
	public abstract int getOutputArity();
	
	/**
	 * Resets the function to its initial state. In the case of a
	 * stateless function, nothing requires to be done.
	 */
	public abstract void reset();
	
	/**
	 * Creates a copy of the function
	 * @return The copy
	 */
	public abstract Function clone();
	
	/**
	 * Populates the set of classes accepted by the function for its
	 * <i>i</i>-th input
	 * @param classes The set of to fill with classes
	 * @param index The index of the input to query
	 */
	public abstract void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index);
	
	/**
	 * Returns the type of the events produced by the function for its
	 * <i>i</i>-th output
	 * @param index The index of the output to query
	 * @return The type of the output
	 */	
	public abstract Class<?> getOutputTypeFor(int index);
	
	public static class ArgumentPlaceholder
	{
		/**
		 * The name of this placeholder
		 */
		private final String m_name;
		
		/**
		 * Creates a new argument placeholder
		 * @param name The name of this placeholder
		 */
		public ArgumentPlaceholder(String name)
		{
			super();
			m_name = name;
		}
		
		/**
		 * Gets the name of this placeholder
		 * @return The name
		 */
		public String getName()
		{
			return m_name;
		}
		
		@Override
		public int hashCode()
		{
			return m_name.hashCode();
		}
		
		@Override
		public boolean equals(Object o)
		{
			if (o == null || !(o instanceof ArgumentPlaceholder))
			{
				return false;
			}
			return m_name.compareTo(((ArgumentPlaceholder) o).m_name) == 0;
		}
	}
}
