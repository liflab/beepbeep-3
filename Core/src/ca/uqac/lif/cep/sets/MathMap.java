/*
    Log trace triaging and etc.
    Copyright (C) 2016 Sylvain Hallé

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

import java.util.HashMap;
import java.util.Map;

/**
 * Implementation of a map with a few extra methods.
 *
 * @param <K> The type of the map's keys
 * @param <V> The type of the map's values
 */
public class MathMap<K,V> extends HashMap<K,V> 
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Gets the index of the key for a given value. If the map
	 * is not injective, any of the keys associated to the value
	 * may be returned.
	 * @param value The value
	 * @return The key, of null if not found
	 */
	public K getWithValue(V value)
	{
		for (Map.Entry<K, V> e : entrySet())
		{
			if (e.getValue().equals(value))
			{
				return e.getKey();
			}
		}
		return null;
	}

}
