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

/**
 * Function of one input and one output
 * @param <T> The type of the input
 * @param <U> The type of the output
 */
public abstract class UnaryFunction<T,U> extends Function
{
	/**
	 * The class of the input
	 */
	private Class<T> m_inputType;

	/**
	 * The class of the output
	 */
	private Class<U> m_outputType;

	/**
	 * Creates a new instance of an unary function
	 * @param t The class of the input
	 * @param u The class of the output
	 */
	public UnaryFunction(Class<T> t, Class<U> u)
	{
		super();
		m_inputType = t;
		m_outputType = u;
	}

	@SuppressWarnings("unchecked")
	@Override
	/*@ requires inputs.length == 1 */
	public void evaluate(/*@NonNull*/ Object[] inputs, Object[] outputs) 
	{
		outputs[0] = getValue((T) inputs[0]);
	}

	/**
	 * Evaluates the function
	 * @param x The argument
	 * @return The return value of the function
	 * @ Any exception occurring during the
	 *   evaluation of the underlying function  
	 */
	public abstract U getValue(T x) ;

	@Override
	public final int getInputArity()
	{
		return 1;
	}

	@Override
	public final int getOutputArity()
	{
		return 1;
	}

	@Override
	public void reset()
	{
		// Do nothing
	}

	@Override
	public UnaryFunction<T,U> duplicate()
	{
		return this;
	}

	@Override
	public final void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
	{
		classes.add(m_inputType);
	}

	@Override
	public Class<?> getOutputTypeFor(int index)
	{
		return m_outputType;
	}
}
