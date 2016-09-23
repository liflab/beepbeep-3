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
package ca.uqac.lif.cep.util;

import java.util.Collection;

/**
 * Utilities for manipulating arrays and collections
 * @author Sylvain Hallé
 */
public class Arrays 
{
	/**
	 * Converts an input object into an array. This method uses the following
	 * rules:
	 * <ul>
	 * <li>If <code>o</code> is an array, return it as is</li>
	 * <li>If <code>o</code> is a collection, turn it into an array
	 *   and return this array</li>
	 * <li>If <code>o</code> is null, return a array of size 0</li>
	 * <li>Otherwise, create an array of size 1, put <code>o</code> inside
	 *   and return this array</li>
	 * </ul>
	 * @param o The object to turn into an array
	 * @return The array
	 */
	public static Object[] toObjectArray(Object o)
	{
		if (o == null)
		{
			return new Object[0];
		}
		else if (o instanceof Object[])
		{
			return (Object[]) o;
		}
		else if (o instanceof Collection<?>)
		{
			return ((Collection<?>) o).toArray();
		}
		Object[] out = new Object[1];
		out[0] = o;
		return out;
	}
}
