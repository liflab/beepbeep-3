/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Implementation of an immutable map
 * <ul>
 * <li>After its instantiation, the object is <em>immutable</em>: all
 *  its fields are declared <code>private final</code> and no method
 *  can ever change their value. (As a matter of fact, all its methods
 *  are also <code>final</code>.) This entails that methods that
 *  normally should be able to modify the contents of a Map (e.g.
 *  <code>put()</code> or <code>clear()</code> here have no effect.</li>
 * <li>Internally, the tuple uses plain arrays (instead of a
 *   <code>HashMap</code>) for storing keys and values. For tuples with,
 *   a small number of keys, this should actually provide <em>faster</em>
 *   access than a HashMap. In all cases, arrays use up less memory
 *   than a HashMap.</li> 
 * <li>Because of this, one can also ask for the <em>index</em> of a key/value
 *   pair, and obtain a value based on its index (rather than its key).
 *   Assuming that all tuples in a stream have their key/value pairs
 *   arranged in the same order, this means one can ask for the index
 *   of a key a first time, and from that point on query the remaining tuples
 *   by directly providing the index.</li>
 * </ul>
 * @author Sylvain Hallé
 *
 */
public final class CacheMap<T> implements Map<String,T>
{
	private String[] m_keys;
	
	private Object[] m_values;
	
	public CacheMap(String[] names)
	{
		super();
		m_keys = names;
		m_values = new Object[m_keys.length];
	}

	@Override
	public final void clear()
	{
		// Do nothing
	}

	@Override
	public final boolean containsKey(Object key)
	{
		if (key == null || !(key instanceof String))
		{
			return false;
		}
		return getIndexOf((String) key) >= 0;
	}

	@Override
	public final boolean containsValue(Object value)
	{
		if (value == null)
		{
			return false;
		}
		for (Object v : m_values)
		{
			if (v.equals(value))
			{
				return true;
			}
		}
		return false;
	}

	@Override
	public final Set<java.util.Map.Entry<String, T>> entrySet()
	{
		// TODO: Don't implement yet
		return null;
	}

	@SuppressWarnings("unchecked")
	@Override
	public final T get(Object key)
	{
		if (key == null || !(key instanceof String))
		{
			return null;
		}
		int i = getIndexOf((String) key);
		if (i >= 0)
		{
			return (T) m_values[i];
		}
		return null;
	}
	
	@SuppressWarnings("unchecked")
	public final Object getValue(int index)
	{
		return (T) m_values[index];
	}
	
	public final int getIndexOf(String s)
	{
		for (int i = 0; i < m_keys.length; i++)
		{
			String k = m_keys[i];
			if (k.compareTo(s) == 0)
			{
				return i;
			}
		}
		return -1;
	}
	
	/**
	 * Retrieves a value, possibly using an index. This allows one
	 * to both get the direct index of a value in the map, if not
	 * known, and to fetch that value.
	 * <pre>
	 * Object o;
	 * cached_index = map.getIndexOf("mykey", cached_index, o);
	 * </pre> 
	 * This will put the value corresponding to <code>mykey</code> in
	 * <code>o</code>, and update <code>cached_index</code> to the
	 * position in the array where this key was found. Later calls
	 * to <code>getIndexOf</code> will use that value to directly
	 * access the element, rather than look for it.
	 * 
	 * @param key The key to get in the map
	 * @param index If negative, the method will look for the key
	 *   in the map to get the value. If greater than or equal to 0,
	 *   the method will directly use that value to fetch the
	 *   object to return.
	 * @param out After the call, will contain a reference to the value
	 *   one is looking for
	 * @return The index value
	 */
	@SuppressWarnings("unchecked")
	public final int getIndexOf(String key, int index, T out)
	{
		if (index >= 0)
		{
			out = (T) m_values[index];
			return index;
		}
		index = getIndexOf(key);
		out = (T) m_values[index];
		return index;
	}

	@Override
	public final boolean isEmpty()
	{
		return m_keys.length == 0;
	}

	@Override
	public final Set<String> keySet()
	{
		Set<String> s = new HashSet<String>();
		for (String name : m_keys)
		{
			s.add(name);
		}
		return s;
	}

	@Override
	public final T put(String key, T value)
	{
		if (key == null)
		{
			return null;
		}
		for (int i = 0; i < m_keys.length; i++)
		{
			if (key.compareTo(m_keys[i]) == 0)
			{
				m_values[i] = value;
				return value;
			}
		}
		return null;
	}
	
	public final void putAt(int index, T value)
	{
		m_values[index] = value;
	}
	
	public final void putAll(T[] values)
	{
		m_values = values;
	}

	@Override
	public final void putAll(Map<? extends String, ? extends T> m)
	{
		// Do nothing
	}

	@Override
	public final T remove(Object key)
	{
		// Do nothing
		return null;
	}

	@Override
	public final int size()
	{
		return m_keys.length;
	}

	@SuppressWarnings("unchecked")
	@Override
	public final Collection<T> values()
	{
		List<T> l = new ArrayList<T>();
		for (Object v : m_values)
		{
			l.add((T) v);
		}
		return l;
	}
}