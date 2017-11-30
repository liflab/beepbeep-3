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

import java.util.List;

import ca.uqac.lif.cep.functions.InvalidArgumentException;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Returns the n-th element of an ordered collection (array or list).
 * @author Sylvain Hallé
 */
public class NthElement extends UnaryFunction<Object,Object>
{
	/**
	 * The position of the element to get
	 */
	protected int m_n;

	/**
	 * Creates a new instance of the function
	 * @param n The position of the element to get
	 */
	public NthElement(int n)
	{
		super(Object.class, Object.class);
		m_n = n;
	}

	@Override
	public Object getValue(Object x)
	{
		if (x.getClass().isArray())
		{
			Object[] array = (Object[]) x;
			try
			{
				return array[m_n];
			}
			catch (ArrayIndexOutOfBoundsException e)
			{
				throw new InvalidArgumentException(this, 0);
			}
		}
		if (x instanceof List<?>)
		{
			List<?> list = (List<?>) x;
			try
			{
				return list.get(m_n);
			}
			catch (IndexOutOfBoundsException e)
			{
				throw new InvalidArgumentException(this, 0);
			}
		}
		throw new InvalidArgumentException(this, 0);
	}

	@Override
	public NthElement duplicate()
	{
		return new NthElement(m_n);
	}

	@Override
	public String toString()
	{
		return m_n + "th of ";
	}
}
