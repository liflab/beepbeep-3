/*
    Log trace triaging and etc.
    Copyright (C) 2016 Sylvain Hall�

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

import java.util.HashSet;

/**
 * Set implementation that behaves like a real set, i.e. two sets
 * are equal if and only if they contain the same elements.
 *
 * @param <T> The type of the set's elements
 */
public class MathSet<T> extends HashSet<T> 
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Creates an empty set
	 */
	public MathSet()
	{
		super();
	}
	
	/**
	 * Creates a set by copying the contents of another set
	 * @param set The other set
	 */
	public MathSet(MathSet<T> set)
	{
		super();
		addAll(set);
	}
	
	@SuppressWarnings("unchecked")
	public MathSet(Object ... objects)
	{
		super();
		for (Object o : objects)
		{
			add((T) o);
		}
	}

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
		if (o == this)
		{
			return true;
		}
		if (o == null || !(o instanceof MathSet))
		{
			return false;
		}
		@SuppressWarnings("unchecked")
		MathSet<T> h = (MathSet<T>) o;
		if (h.size() != size())
		{
			return false;
		}
		for (T st : this)
		{
			if (!h.contains(st))
			{
				return false;
			}
		}
		return true;
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("{");
		boolean first = true;
		for (T e : this)
		{
			if (first)
			{
				first = false;
			}
			else
			{
				out.append(",");
			}
			out.append(e);
		}
		out.append("}");
		return out.toString();
	}
}
