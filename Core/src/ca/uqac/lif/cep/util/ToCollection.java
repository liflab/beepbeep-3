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

/**
 * Converts a front of <i>n</i> input events into a collection of
 * <i>n</i> objects. 
 * @author Sylvain Hallé
 */
public abstract class ToCollection extends Function
{
	/**
	 * An array that keeps the types of each input stream
	 */
	protected Class<?>[] m_types;
	
	/**
	 * Creates a new ToList function
	 * @param types The types of each input stream
	 */
	public ToCollection(Class<?> ... types)
	{
		super();
		m_types = types;
	}
	
	@Override
	public int getInputArity() 
	{
		return m_types.length;
	}

	@Override
	public int getOutputArity() 
	{
		return 1;
	}

	@Override
	public void reset() 
	{
		// Nothing to do
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index)
	{
		classes.add(m_types[index]);
	}
	
	/**
	 * Converts a front of <i>n</i> events into an array of
	 * <i>n</i> objects. In such a case, the list preserves the ordering
	 * of the events: element <i>i</i> corresponds to the <i>i</i>-th
	 * input stream.
	 */
	public static class ToArray extends ToCollection
	{
		public ToArray(Class<?> ... types)
		{
			super(types);
		}
		
		@Override
		public Class<?> getOutputTypeFor(int index) 
		{
			return (new Object[]{}).getClass();
		}

		@Override
		public ToArray duplicate() 
		{
			return new ToArray(m_types);
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			Object[] out = new Object[inputs.length];
			for (int i = 0; i < inputs.length; i++)
			{
				out[i] = inputs[i];
			}
			outputs[0] = out;
		}
	}
	
	/**
	 * Converts a front of <i>n</i> events into a list of
	 * <i>n</i> objects. In such a case, the list preserves the ordering
	 * of the events: element <i>i</i> corresponds to the <i>i</i>-th
	 * input stream.
	 */
	public static class ToList extends ToCollection
	{
		public ToList(Class<?> ... types)
		{
			super(types);
		}

		@Override
		public ToList duplicate() 
		{
			return new ToList(m_types);
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			List<Object> out = new ArrayList<Object>(inputs.length);
			for (int i = 0; i < inputs.length; i++)
			{
				out.add(inputs[i]);
			}
			outputs[0] = out;
		}

		@Override
		public Class<?> getOutputTypeFor(int index) 
		{
			return List.class;
		}
	}
	
	/**
	 * Converts a front of <i>n</i> events into a set of
	 * <i>n</i> objects.
	 */
	public static class ToSet extends ToCollection
	{
		public ToSet(Class<?> ... types)
		{
			super(types);
		}

		@Override
		public ToSet duplicate() 
		{
			return new ToSet(m_types);
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			Set<Object> out = new HashSet<Object>(inputs.length);
			for (int i = 0; i < inputs.length; i++)
			{
				out.add(inputs[i]);
			}
			outputs[0] = out;
		}

		@Override
		public Class<?> getOutputTypeFor(int index) 
		{
			return Set.class;
		}
	}
}
