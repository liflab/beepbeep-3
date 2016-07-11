/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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

import java.util.Set;

/**
 * Represents a stateless <i>m</i>-to-<i>n</i> function.
 * 
 * @author Sylvain Hallé
 */
public interface Function extends Cloneable
{
	/**
	 * The maximum input arity that a function can have
	 */
	public static int s_maxInputArity = 10;
	
	/**
	 * Computes the outputs of the function, given some inputs
	 * @param inputs The arguments of the function. The size of the array
	 *   should be equal to the function's declared input arity.
	 * @return The outputs of the function. The size of the array returned
	 *   should be equal to the function's declared output arity.
	 */
	public Object[] compute(Object[] inputs);
	
	/**
	 * Gets the function's input arity, i.e. the number of arguments
	 * it takes.
	 * @return The input arity
	 */
	public int getInputArity();
	
	/**
	 * Gets the function's output arity, i.e. the number of elements
	 * it outputs. (We expect that most functions will have an output
	 * arity of 1.)
	 * @return The output arity
	 */
	public int getOutputArity();
	
	/**
	 * Resets the function to its initial state. In the case of a
	 * stateless function, nothing requires to be done.
	 */
	public void reset();
	
	/**
	 * Creates a copy of the function
	 * @return The copy
	 */
	public Function clone();
	
	/**
	 * Populates the set of classes accepted by the function for its
	 * <i>i</i>-th input
	 * @param classes The set of to fill with classes
	 * @param index The index of the input to query
	 */
	public void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index);
	
	/**
	 * Returns the type of the events produced by the function for its
	 * <i>i</i>-th output
	 * @param index The index of the output to query
	 * @return The type of the output
	 */	
	public Class<?> getOutputTypeFor(int index);
}
