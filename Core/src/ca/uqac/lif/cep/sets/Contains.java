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

import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * Checks if a multiset contains an element.
 * 
 * @author Sylvain Hallé
 */
@SuppressWarnings("rawtypes")
public class Contains extends BinaryFunction<Set, Object, Boolean>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 3805319331641617083L;
	public static final transient Contains instance = new Contains();

	private Contains()
	{
		super(Set.class, Object.class, Boolean.class);
	}

	@Override
	public Boolean getValue(Set x, Object y)
	{
		if (x == null || y == null)
		{
			return false;
		}
		return x.contains(y);
	}

	@Override
	public String toString()
	{
		return "contains";
	}
}
