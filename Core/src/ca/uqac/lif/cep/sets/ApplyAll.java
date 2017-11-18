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
package ca.uqac.lif.cep.sets;

import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Given a multiset/array, returns a <em>new</em> multiset/array whose content is
 * the result of applying a function to each element.
 * 
 * @author Sylvain Hallé
 */
public class ApplyAll extends UnaryFunction<Object,Object>
{
	/**
	 * The function to apply on each element
	 */
	protected Function m_function;

	public ApplyAll()
	{
		super(Object.class, Object.class);
	}

	public ApplyAll(Function function)
	{
		this();
		m_function = function;
	}

	/**
	 * Sets the function to apply on each element
	 * @param function The condition
	 */
	public void setCondition(Function function)
	{
		m_function = function;
	}

	@Override
	public Object getValue(Object x) throws FunctionException
	{
		if (x instanceof Multiset)
		{
			Multiset out = new Multiset();
			for (Object o : (Multiset) x)
			{
				Object[] in = new Object[1];
				in[0] = o;
				Object[] values = new Object[1];
				m_function.evaluate(in, values);
				out.add(values[0]);
			}
			return out;
		}
		Object[] in_array = (Object[]) x;
		Object[] out = new Object[in_array.length];
		for (int i = 0; i < in_array.length; i++)
		{
			Object[] in = new Object[1];
			in[0] = in_array[i];
			Object[] values = new Object[1];
			m_function.evaluate(in, values);
			out[i] = values[0];
		}
		return out;
	}
}
