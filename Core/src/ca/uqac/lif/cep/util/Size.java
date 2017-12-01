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

import java.util.Collection;
import java.util.Map;

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Evaluates the size of an object. The "size" is defined as follows:
 * <ul>
 * <li>For a string, the length</li>
 * <li>For a number, the integer value</li>
 * <li>For a collection, a map or an array, the cardinality</li>
 * <li>For anything else (including <tt>null</tt>), 0</li>
 * </ul>
 * 
 * @author Sylvain Hallé
 */
@SuppressWarnings("rawtypes")
public class Size extends UnaryFunction<Object,Integer>
{
	public static final transient Size instance = new Size();

	protected Size()
	{
		super(Object.class, Integer.class);
	}

	@Override
	public Integer getValue(Object x)
	{
		if (x == null)
		{
			return 0;
		}
		if (x instanceof String)
		{
			return ((String) x).length();
		}
		if (x instanceof Number)
		{
			return ((Number) x).intValue();
		}
		if (x instanceof Map)
		{
			return ((Map) x).size();
		}
		if (x instanceof Collection)
		{
			return ((Collection) x).size();
		}
		if (x.getClass().isArray())
		{
			return ((Object[]) x).length;
		}
		return 0;
	}
}
