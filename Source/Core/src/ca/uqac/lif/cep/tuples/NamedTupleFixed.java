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
package ca.uqac.lif.cep.tuples;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of a named tuple. Contrarily to a {@link NamedTupleMap},
 * a fixed tuple assumes stronger hypotheses on its use in order to
 * reduce memory usage and increase response time.
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
 * <p>The process can be further optimized by using the 
 * {@link FixedTupleBuilder} class to build a stream of tuples that all follow
 * the same schema.
 * <p>Note that if these constraints are not suitable for your processing,
 * you should use the "regular" {@link NamedTupleMap} class that gives you
 * much more flexibility (possibly at the expense of some overhead).
 * @author Sylvain Hallé
 *
 */
public final class NamedTupleFixed extends NamedTuple
{
	private final String[] m_names;
	
	private final Object[] m_values;
	
	public NamedTupleFixed(String[] names, Object[] values)
	{
		super();
		m_names = names;
		m_values = values;
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
	public final Set<java.util.Map.Entry<String, Object>> entrySet()
	{
		// Don't implement this for now
		return null;
	}

	@Override
	public final Object get(Object key)
	{
		if (key == null || !(key instanceof String))
		{
			return null;
		}
		int i = getIndexOf((String) key);
		if (i >= 0)
		{
			return m_values[i];
		}
		return null;
	}
	
	public final Object getValue(int index)
	{
		return m_values[index];
	}
	
	public final int getIndexOf(String s)
	{
		for (int i = 0; i < m_names.length; i++)
		{
			String k = m_names[i];
			if (k.compareTo(s) == 0)
			{
				return i;
			}
		}
		return -1;
	}

	@Override
	public final boolean isEmpty()
	{
		return m_names.length == 0;
	}

	@Override
	public final Set<String> keySet()
	{
		Set<String> s = new HashSet<String>();
		for (String name : m_names)
		{
			s.add(name);
		}
		return s;
	}

	@Override
	public final EmlConstant put(String key, Object value)
	{
		// Do nothing
		return null;
	}

	@Override
	public final void putAll(Map<? extends String, ? extends Object> m)
	{
		// Do nothing
	}

	@Override
	public final EmlConstant remove(Object key)
	{
		// Do nothing
		return null;
	}

	@Override
	public final int size()
	{
		return m_names.length;
	}

	@Override
	public final Collection<Object> values()
	{
		List<Object> l = new ArrayList<Object>();
		for (Object v : m_values)
		{
			l.add(v);
		}
		return l;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		return wrapObject(this);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("(");
		for (int i = 0; i < m_names.length; i++)
		{
			if (i > 0)
			{
				out.append(",");
			}
			out.append("(").append(m_names[i]).append(",");
			if (i < m_values.length)
			{
				out.append(m_values[i]);
			}
			else
			{
				out.append("?");
			}
			out.append(")");
		}
		out.append(")");
		return out.toString();
	}
	
	@Override
	public NamedTupleFixed clone()
	{
		return new NamedTupleFixed(m_names, m_values);
	}

}
