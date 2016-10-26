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

import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * Applies a function to input events to produce output events. This 
 * class provides a way to "lift" any <i>m</i>-to-<i>n</i> function
 * into an <i>m</i>-to-<i>n</i> processor, by simply calling the
 * function on the inputs to produce the outputs.
 * 
 * @author Sylvain Hallé
 *
 */
public class FunctionProcessor extends SingleProcessor
{
	/**
	 * The object responsible for the computation
	 */
	protected final Function m_function;
	
	/**
	 * Instantiates a new function processor
	 * @param comp The computable object responsible for the computation
	 */
	public FunctionProcessor(Function comp)
	{
		super(comp.getInputArity(), comp.getOutputArity());
		m_function = comp;
	}
	
	@Override
	public void reset()
	{
		m_function.reset();
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		return wrapVector(m_function.evaluate(inputs, m_context));
	}
	
	@Override
	public FunctionProcessor clone()
	{
		FunctionProcessor out = new FunctionProcessor(m_function.clone(m_context));
		return out;
	}
	
	@Override
	public final void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
	{
		// The type is determined by that of the underlying function
		m_function.getInputTypesFor(classes, index);
	}
	
	@Override
	public final Class<?> getOutputTypeFor(int index)
	{
		// The type is determined by that of the underlying function
		return m_function.getOutputTypeFor(index);
	}
	
	@Override
	public void setContext(Context context)
	{
		super.setContext(context);
		m_function.setContext(context);
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		super.setContext(key, value);
		m_function.setContext(key, value);
	}
	
	@Override
	public String toString()
	{
		return m_function.toString();
	}
	
	/**
	 * Gets the function associated to that processor
	 * @return The function
	 */
	public Function getFunction()
	{
		return m_function;
	}
}
