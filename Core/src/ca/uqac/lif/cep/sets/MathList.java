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

import java.util.ArrayList;

/**
 * List implementation that behaves like a real list, i.e. two lists
 * are equal if and only if they contain the same elements in the
 * same order.
 *
 * @param <T> The type of the lists's elements
 */
public class MathList<T> extends ArrayList<T> 
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;

	@Override
	public int hashCode()
	{
		int code = 0;
		for (T t : this)
		{
			code += t.hashCode();
		}
		return code;
	}
	
	@Override
	public boolean equals(Object o)
	{
		if (o == null || !(o instanceof MathList))
		{
			return false;
		}
		if (o == this)
		{
			return true;
		}
		@SuppressWarnings("unchecked")
		MathList<T> h = (MathList<T>) o;
		if (h.size() != size())
		{
			return false;
		}
		for (int i = 0; i < size(); i++)
		{
			T e1 = get(i);
			T e2 = h.get(i);
			if (!e1.equals(e2))
			{
				return false;
			}
		}
		return true;
	}
}
