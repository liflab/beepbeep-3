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
package ca.uqac.lif.cep.util;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.InvalidArgumentException;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Given a set/list/array, returns a <em>new</em> set/list/array whose 
 * content is the result of applying a function to each element.
 * 
 * @author Sylvain Hallé
 */
public class ApplyToAll extends UnaryFunction<Object,Object>
{
	/**
	 * The function to apply on each element
	 */
	protected Function m_function;

	public ApplyToAll()
	{
		super(Object.class, Object.class);
	}

	public ApplyToAll(Function function)
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
	public Object getValue(Object x) 
	{
		if (x instanceof List)
		{
			List<Object> out = new ArrayList<Object>(((List<?>) x).size());
			for (Object o : (List<?>) x)
			{
				Object[] in = new Object[1];
				in[0] = o;
				Object[] values = new Object[1];
				m_function.evaluate(in, values);
				out.add(values[0]);
			}
			return out;
		}
		if (x instanceof Set)
		{
			Set<Object> out = new HashSet<Object>();
			for (Object o : (Set<?>) x)
			{
				Object[] in = new Object[1];
				in[0] = o;
				Object[] values = new Object[1];
				m_function.evaluate(in, values);
				out.add(values[0]);
			}
			return out;
		}
		if (x.getClass().isArray())
		{
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
		throw new InvalidArgumentException(this, 0);
	}
}
