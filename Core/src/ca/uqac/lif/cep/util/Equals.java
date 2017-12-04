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

import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * Checks for the equality of various data types
 * @author Sylvain Hallé
 */
public class Equals extends BinaryFunction<Object,Object,Boolean>
{
	public static final transient Equals instance = new Equals();

	private Equals()
	{
		super(Object.class, Object.class, Boolean.class);
	}

	@Override
	public Boolean getValue(Object x, Object y)
	{
		if (x == null || y == null)
		{
			return false;
		}
		if (x instanceof Collection && y instanceof Collection)
		{
			Collection<?> set_x = (Collection<?>) x;
			Collection<?> set_y = (Collection<?>) y;
			return set_x.size() == set_y.size() && set_x.containsAll(set_y);
		}
		if (x instanceof String && y instanceof String)
		{
			return ((String) x).compareTo((String) y) == 0;
		}
		return x.equals(y);
	}

	@Override
	public String toString()
	{
		return "=";
	}
}