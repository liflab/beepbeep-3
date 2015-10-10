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
package ca.uqac.lif.cep.eml.tuples;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class NamedTupleMap extends NamedTuple 
{
	protected Map<String,Object> m_contents;
	
	public NamedTupleMap()
	{
		super();
		m_contents = new HashMap<String,Object>();
	}
	
	/* From this point on, these are merely delegate methods
	 * for the inner Map object
	 */

	@Override
	public void clear()
	{
		m_contents.clear();
	}

	@Override
	public boolean containsKey(Object arg0)
	{
		return m_contents.containsKey(arg0);
	}

	public boolean containsValue(Object value) {
		return m_contents.containsValue(value);
	}

	public Set<java.util.Map.Entry<String, Object>> entrySet() 
	{
		return m_contents.entrySet();
	}

	public boolean equals(Object o) 
	{
		return m_contents.equals(o);
	}

	public Object get(Object key) 
	{
		return m_contents.get(key);
	}

	public int hashCode() 
	{
		return m_contents.hashCode();
	}

	public boolean isEmpty() 
	{
		return m_contents.isEmpty();
	}

	public Set<String> keySet() 
	{
		return m_contents.keySet();
	}

	public Object put(String key, Object value) 
	{
		return m_contents.put(key, value);
	}

	public void putAll(Map<? extends String, ? extends Object> m) 
	{
		m_contents.putAll(m);
	}

	public Object remove(Object key) 
	{
		return m_contents.remove(key);
	}

	public int size() 
	{
		return m_contents.size();
	}

	public Collection<Object> values() 
	{
		return m_contents.values();
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("(");
		boolean first = true;
		for (String name : m_contents.keySet())
		{
			if (!first)
			{
				out.append(",");
			}
			Object value = m_contents.get(name);
			out.append(name).append("=").append(value);
			first = false;
		}
		out.append(")");
		return out.toString();
	}
	
	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		return wrapObject(this);
	}
}
