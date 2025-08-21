/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2024 Sylvain Hallé

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

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.UnaryFunction;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * A container object for map functions and processors. Some functions come in
 * two flavors:
 * <ul>
 * <li>The "plain" function takes as input a map object and returns the
 * <em>same</em> object, to which a modification has been applied. Note
 * however that in this case, a call to {@link Processor#reset() reset()}
 * still results in the instantiation of a <em>new</em> map instance.</li>
 * <li>The "new" function takes as input a map object, and returns a <em>new
 * copy</em> of the object with the modification made to it.</li>
 * </ul>
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class Maps
{
	/**
	 * Extracts the set of values of a map
	 */
	public static final transient Values values = new Values();

	/**
	 * Extracts the multi-set of values of a map
	 */
	public static final transient MultiValues multiValues = new MultiValues();

	protected Maps()
	{
		// Utility class
	}

	/**
	 * Gets the set of values in a map.
	 * @since 0.7
	 */
	@SuppressWarnings("rawtypes")
	public static class Values extends UnaryFunction<Map, Collection>
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
			Collection<?> col = x.values();
			col.remove(null);
			return col;
		}
	}
	
	/**
	 * Gets the set of keys in a map.
	 * @since 0.11.3
	 */
	@SuppressWarnings("rawtypes")
	public static class Keys extends UnaryFunction<Map, Collection>
	{
		/**
		 * A single instance of the function
		 */
		public static final transient Keys instance = new Keys();

		protected Keys()
		{
			super(Map.class, Collection.class);
		}

		@Override
		public Collection<?> getValue(Map x)
		{
			Collection<?> col = x.keySet();
			col.remove(null);
			return col;
		}
	}

	/**
	 * Gets the multi-set of values in a map. This means that the same
	 * value occurring multiple times will be there multiple times as
	 * well.
	 * @since 0.10.3
	 */
	@SuppressWarnings("rawtypes")
	public static class MultiValues extends UnaryFunction<Map, Collection>
	{
		/**
		 * A single instance of the function
		 */
		public static final transient MultiValues instance = new MultiValues();

		protected MultiValues()
		{
			super(Map.class, Collection.class);
		}

		@Override
		public Collection<?> getValue(Map x)
		{
			Multiset set = new Multiset();
			for (Object o : x.entrySet())
			{
				Map.Entry<?,?> e  = (Map.Entry<?,?>) o;
				set.add(e.getValue());
			}
			return set;
		}
	}

	/**
	 * Gets a value in the map, based on the name of a key.
	 * @since 0.7
	 */
	@SuppressWarnings("rawtypes")
	public static class Get extends UnaryFunction<Map, Object>
	{
		/**
		 * The key to get from the map.
		 */
		protected final String m_key;

		/**
		 * The default value to return if the key is not defined in the map.
		 */
		protected final Object m_default;

		/**
		 * Creates a new get function.
		 * 
		 * @param key
		 *          The key to get from the map
		 * @param default_value
		 *          The default value to return if the
		 *          key is not defined in the map
		 * @since 0.11.2
		 */
		public Get(String key, Object default_value)
		{
			super(Map.class, Object.class);
			m_key = key;
			m_default = default_value;
		}

		/**
		 * Creates a new get function.
		 * 
		 * @param key
		 *          The key to get from the map
		 */
		public Get(String key)
		{
			this(key, null);
		}

		@SuppressWarnings("unchecked")
		@Override
		public Object getValue(Map x)
		{
			if (x.containsKey(m_key))
			{
				return x.get(m_key);
			}
			return m_default;
		}
	}

	/**
	 * Updates a map by putting key-value pairs into it. The processor takes two
	 * input streams; the first contains the key, and the second contains the value.
	 * @since 0.7
	 */
	public static class PutInto extends UniformProcessor
	{
		/**
		 * The underlying map
		 */
		protected Map<Object, Object> m_map;

		/**
		 * Create a new instance of the processor
		 */
		public PutInto()
		{
			super(2, 1);
			m_map = new HashMap<Object, Object>();
		}

		@Override
		public void reset()
		{
			super.reset();
			m_map = new HashMap<Object, Object>();
		}

		@Override
		public PutInto duplicate(boolean with_state)
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
	 * Updates a map by putting key-value pairs into it. The processor takes a
	 * single input stream, whose events are <em>arrays</em>. The first element of
	 * the array contains the key, and the second contains the value.
	 */
	public static class MapPutInto extends UniformProcessor
	{
		/**
		 * The underlying map
		 */
		protected Map<Object, Object> m_map;

		/**
		 * Create a new instance of the processor
		 */
		public MapPutInto()
		{
			super(1, 1);
			m_map = new HashMap<Object, Object>();
		}

		@Override
		public void reset()
		{
			super.reset();
			m_map = new HashMap<Object, Object>();
		}

		@Override
		public MapPutInto duplicate(boolean with_state)
		{
			return new MapPutInto();
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

	/**
	 * Creates a new map by applying a function to all the values of
	 * a map given as input
	 */
	@SuppressWarnings("rawtypes")
	public static class ApplyAll extends UnaryFunction<Map,Map>
	{
		/**
		 * The function to apply to each value of the map
		 */
		protected Function m_function;

		/**
		 * Creates a new {@code ApplyAll} function
		 * @param f The function to apply to all the values. Must be
		 * a 1:1 function.
		 */
		//@ requires f.getInputArity() == 1
		//@ requires f.getOutputArity() == 1
		public ApplyAll(/*@ non_null @*/ Function f)
		{
			super(Map.class, Map.class);
			m_function = f;
		}

		@SuppressWarnings("unchecked")
		@Override
		public Map getValue(Map x)
		{
			Map<Object,Object> out = new HashMap<Object,Object>();
			Object[] a_out = new Object[1];
			for (Object o  : x.entrySet())
			{
				Map.Entry<Object,Object> e = (Map.Entry<Object,Object>) o;
				m_function.evaluate(new Object[]{e.getValue()}, a_out);
				out.put(e.getKey(), a_out[0]);
			}
			return out;
		}
	}

	/**
	 * Updates a map by merging its contents with a stream of incoming maps.
	 * The output of this processor is a map with arbitrary keys, and sets
	 * as values.
	 */
	public static class MergeMaps extends UniformProcessor
	{
		/**
		 * The map that is being updated
		 */
		protected Map<Object,Set<Object>> m_map;

		/**
		 * Creates a new merge processor.
		 */
		public MergeMaps()
		{
			super(1, 1);
			m_map = new HashMap<Object,Set<Object>>();
		}

		@Override
		protected boolean compute(Object[] inputs, Object[] outputs)
		{
			Map<?,?> m = (Map<?,?>) inputs[0];
			for (Object m_o : m.entrySet())
			{
				if (m_o instanceof Map.Entry)
				{
					Map.Entry<?,?> e  = (Map.Entry<?,?>) m_o;
					Object key = e.getKey();
					Object value = e.getValue();
					if (value == null)
					{
						outputs[0] = m_map;
						return true;
					}
					Set<Object> s_value;
					if (m_map.containsKey(key))
					{
						s_value = m_map.get(key);
					}
					else
					{
						s_value = new HashSet<Object>();
					}
					if (value instanceof Collection)
					{
						s_value.addAll((Collection<?>) value);
					}
					else
					{
						s_value.add(value);
					}
					m_map.put(key, s_value);
				}
			}
			outputs[0] = m_map;
			return true;
		}

		@Override
		public void reset()
		{
			super.reset();
			m_map.clear();
		}

		@Override
		public MergeMaps duplicate(boolean with_state)
		{
			MergeMaps mm = new MergeMaps();
			if (with_state)
			{
				for (Map.Entry<Object,Set<Object>> e : m_map.entrySet())
				{
					HashSet<Object> new_set = new HashSet<Object>();
					new_set.addAll(e.getValue());
					mm.m_map.put(e.getKey(), new_set);
				}
			}
			return mm;
		}
	}

	/**
	 * Filters a map based on a condition on its key-value pairs.
	 * @since 0.11.3
	 */
	@SuppressWarnings("rawtypes")
	public static class FilterMap extends UnaryFunction<Map,Map>
	{
		/**
		 * The function that is called to determine if a key-value pair should be
		 * included in the output map.
		 */
		protected final Function m_condition;

		/**
		 * Creates a new instance of the function.
		 * @param f A 2:1 function that receives a key and a value, and
		 * should return {@link Boolean.TRUE} if this key-value pair should be
		 * included in the output map.
		 */
		//@ requires f.getInputArity() == 2
		//@ requires f.getOutputArity() == 1
		public FilterMap(/*@ non_null @*/ Function f)
		{
			super(Map.class, Map.class);
			m_condition = f;
		}

		@Override
		public Map getValue(Map m)
		{
			Map<Object,Object> out_map = new HashMap<Object,Object>();
			for (Object k : m.keySet())
			{
				Object v = m.get(k);
				Object[] out = new Object[1];
				m_condition.evaluate(new Object[] {k, v}, out);
				if (Boolean.TRUE.equals(out[0]))
				{
					out_map.put(k, v);
				}
			}
			return out_map;
		}

		@Override
		public FilterMap duplicate(boolean with_state)
		{
			return new FilterMap(m_condition);
		}
	}

	/**
	 * A map that implements equality based on its contents. Two mathmaps are
	 * equal if they have equal keys, and for each key, the associated value is
	 * equal.
	 *
	 * @param <K> The type of the keys
	 * @param <V> The type of the values
	 */
	public static class MathMap<K,V> extends HashMap<K,V>
	{
		/**
		 * Dummy UID.
		 */
		private static final long serialVersionUID = 1L;

		@Override
		public boolean equals(Object o)
		{
			if (!(o instanceof MathMap))
			{
				return false;
			}
			MathMap<?,?> map = (MathMap<?,?>) o;
			if (map.size() != size())
			{
				return false;
			}
			for (Map.Entry<K,V> e : entrySet())
			{
				if (!map.containsKey(e.getKey()))
				{
					return false;
				}
				Object v = map.get(e.getKey());
				if (!Equals.isEqualTo(e.getValue(), v))
				{
					return false;
				}
			}
			return true;
		}

		@Override
		public int hashCode()
		{
			return size();
		}
	}
}
