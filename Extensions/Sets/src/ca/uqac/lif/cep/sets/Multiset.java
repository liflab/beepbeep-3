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

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * A set where each element can be present more than once
 */
public class Multiset implements Set<Object>
{
	/**
	 * The map used to store the relation between each element and its
	 * cardinality
	 */
	private final Map<Object,Integer> m_map;
	
	/**
	 * Creates an empty multiset
	 */
	public Multiset()
	{
		super();
		m_map = new HashMap<Object, Integer>();
	}
	
	/**
	 * Performs the union of two multisets
	 * @param b The multiset to add
	 * @return This multiset
	 */
	public Multiset addAll(Multiset b)
	{
		for (Object o : b.keySet())
		{
			if (!m_map.containsKey(o))
			{
				m_map.put(o, b.get(o));
			}
			else
			{
				int cardinality = m_map.get(o) + b.get(o);
				m_map.put(o, cardinality);
			}
		}
		return this;
	}
	
	/**
	 * Picks one element of the multiset. This assumes you don't care
	 * about what element of the multiset you get, as long as you get one.
	 * @return An element of the multiset, or null if the multiset is empty
	 */
	public Object getAnyElement()
	{
		Set<Object> objects = m_map.keySet();
		for (Object o : objects)
		{
			// Return the first element you pick
			return o;
		}
		return null;
	}
	
	/**
	 * Checks if an element is contained (at least once) into this multiset
	 * @param o The element
	 * @return true if the element is contained at least once, false otherwise
	 */
	public boolean contains(Object o)
	{
		if (!m_map.containsKey(o))
		{
			return false;
		}
		int cardinality = m_map.get(o);
		return cardinality > 0;
	}
	
	/**
	 * Adds an element to this multiset
	 * @param o The element
	 * @return This multiset
	 */
	public Multiset addElement(Object o)
	{
		if (!m_map.containsKey(o))
		{
			m_map.put(o, 1);
		}
		int cardinality = m_map.get(o);
		m_map.put(o,  cardinality + 1);
		return this;
	}
	
	/**
	 * Gets the cardinality of an element
	 * @param o The element
	 * @return The cardinality
	 */
	public int get(Object o)
	{
		if (!m_map.containsKey(o))
		{
			return 0;
		}
		return m_map.get(o);
	}
	
	/**
	 * Gets the (normal) set of all elements in this multiset.
	 * In other words, turns this multiset into a regular set. 
	 * @return The set of elmeents
	 */
	public Set<Object> keySet()
	{
		return m_map.keySet();
	}
	
	/**
	 * Removes an element from this multiset
	 * @param o The element
	 * @return This multiset
	 */
	public Multiset removeElement(Object o)
	{
		if (m_map.containsKey(o))
		{
			int cardinality = m_map.get(o);
			if (cardinality == 1)
			{
				m_map.remove(o);
			}
			else
			{
				m_map.put(o,  cardinality - 1);
			}
		}
		return this;
	}
	
	/**
	 * Gets the size of the multiset
	 * @return The size
	 */
	@Override
	public int size()
	{
		int size = 0;
		for (int i : m_map.values())
		{
			size += i;
		}
		return size;
	}
	
	@Override
	public void clear()
	{
		m_map.clear();
	}
	
	@Override
	public String toString()
	{
		return m_map.toString();
	}

	@Override
	public boolean add(Object arg0) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addAll(Collection<? extends Object> arg0) 
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean containsAll(Collection<?> arg0) 
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isEmpty() 
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Iterator<Object> iterator() 
	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean remove(Object arg0) 
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean removeAll(Collection<?> arg0) 
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean retainAll(Collection<?> arg0) 
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Object[] toArray() 
	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <T> T[] toArray(T[] arg0) 
	{
		// TODO Auto-generated method stub
		return null;
	}
}
