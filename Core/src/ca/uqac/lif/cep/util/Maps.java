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

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * A container object for map functions and processors.
 * Some functions come in two flavors:
 * <ul>
 * <li>The "plain" function takes as input a map object and returns the
 * <em>same</em> object</li>, to which a modification has been applied
 * <li>The "new" function takes as input a map object, and returns a
 * <em>new copy</em> of the object with the modification made to it</li>
 * </ul>
 * @author Sylvain Hallé
 */
public class Maps
{
	private Maps()
	{
		// Utility class
	}
	
	/**
	 * Gets the set of values in a map
	 */
	@SuppressWarnings("rawtypes")
	public static class Values extends UnaryFunction<Map,Collection>
	{
		/**
		 * A single instance of the function
		 */
		public static final transient Values instance = new Values();
		
		protected Values()
		{
			super(Map.class, Collection.class);
		}

		@Override
		public Collection<?> getValue(Map x) 
		{
			return x.values();
		}
	}
	
	/**
	 * Updates a map by putting key-value pairs into it. The processor
	 * takes two input streams; the first contains the key, and the second
	 * contains the value.
	 */
	public static class PutInto extends UniformProcessor
	{
		/**
		 * The underlying map
		 */
		protected Map<Object,Object> m_map;
		
		/**
		 * Create a new instance of the processor
		 */
		public PutInto()
		{
			super(2, 1);
			m_map = new HashMap<Object,Object>();
		}
		
		@Override
		public void reset()
		{
			m_map.clear();
		}

		@Override
		public PutInto duplicate()
		{
			return new PutInto();
		}

		@Override
		protected boolean compute(Object[] inputs, Object[] outputs) 
		{
			m_map.put(inputs[0], inputs[1]);
			outputs[0] = m_map;
			return true;
		}
		
		@Override
		public Class<?> getOutputType(int index)
		{
			return Map.class;
		}
	}
	
	/**
	 * Updates a map by putting key-value pairs into it. The processor
	 * takes a single input stream, whose events are <em>arrays</em>. The first
	 * element of the array contains the key, and the second
	 * contains the value.
	 */
	public static class ArrayPutInto extends UniformProcessor
	{
		/**
		 * The underlying map
		 */
		protected Map<Object,Object> m_map;
		
		/**
		 * Create a new instance of the processor
		 */
		public ArrayPutInto()
		{
			super(1, 1);
			m_map = new HashMap<Object,Object>();
		}
		
		@Override
		public void reset()
		{
			m_map.clear();
		}

		@Override
		public ArrayPutInto duplicate()
		{
			return new ArrayPutInto();
		}

		@Override
		protected boolean compute(Object[] inputs, Object[] outputs) 
		{
			m_map.put(((Object[]) inputs[0])[0], ((Object[]) inputs[0])[1]);
			outputs[0] = m_map;
			return true;
		}
		
		@Override
		public Class<?> getOutputType(int index)
		{
			return Map.class;
		}
	}
}
