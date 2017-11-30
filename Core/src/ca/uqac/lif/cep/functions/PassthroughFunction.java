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
package ca.uqac.lif.cep.functions;

import java.util.Set;

import ca.uqac.lif.cep.Context;

/**
 * Delegates all calls of the {@link Function} class to an internal
 * object instantiated by a method.
 * <p>
 * The main purpose of this class is to allow one to create a class
 * out of a {@link FunctionTree} instance created programmatically. The code
 * creating the <code>FunctionTree</code> is written in the
 * {@link #getFunction()} method (which, as a matter of fact, can
 * return any other <code>Function</code> object).
 * 
 * @author Sylvain Hallé
 *
 */
public abstract class PassthroughFunction extends Function
{
	/**
	 * The function to which all calls will be delegated
	 */
	private Function m_function;

	/**
	 * Createa a new instance of PassthroughFunction
	 */
	public PassthroughFunction()
	{
		super();
		m_function = getFunction();
	}

	/**
	 * Instantiates the function that this object will call
	 * @return The function
	 */
	public abstract Function getFunction();

	@Override
	public final void evaluate(Object[] inputs, Object[] outputs, Context context) 
	{
		m_function.evaluate(inputs, outputs, context);
	}

	@Override
	public final void evaluate(Object[] inputs, Object[] outputs) 
	{
		m_function.evaluate(inputs, outputs);
	}

	@Override
	public final int getInputArity()
	{
		return m_function.getInputArity();
	}

	@Override
	public final int getOutputArity()
	{
		return m_function.getOutputArity();
	}

	@Override
	public final void reset()
	{
		m_function.reset();
	}

	@Override
	public final Function duplicate()
	{
		return this;
	}

	@Override
	public final void getInputTypesFor(Set<Class<?>> classes, int index)
	{
		m_function.getInputTypesFor(classes, index);
	}

	@Override
	public final Class<?> getOutputTypeFor(int index)
	{
		return m_function.getOutputTypeFor(index);
	}

}
