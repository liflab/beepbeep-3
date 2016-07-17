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

import java.util.Set;

import ca.uqac.lif.cep.BinaryFunction;

/**
 * Evaluates if the first set is a subset or is equal to the second set.
 * 
 * @author Sylvain Hallé
 */
public class IsSubsetOrEqual extends BinaryFunction<Object,Object,Boolean>
{
	public static final transient IsSubsetOrEqual instance = new IsSubsetOrEqual();
	
	IsSubsetOrEqual()
	{
		super(Object.class, Object.class, Boolean.class);
	}

	@Override
	public Boolean evaluate(Object x, Object y)
	{
		if (x instanceof Set<?> && y instanceof Set<?>)
		{
			Set<?> set_x = (Set<?>) x;
			Set<?> set_y = (Set<?>) y;
			return set_y.containsAll(set_x);
		}
		return false;
	}
}
