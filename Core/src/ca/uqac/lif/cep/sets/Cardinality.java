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

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Evaluates the cardinality of a set or a multiset
 * 
 * @author Sylvain Hallé
 */
@SuppressWarnings("rawtypes")
public class Cardinality extends UnaryFunction<Set, Integer>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 3469690418825982252L;
	public static final transient Cardinality instance = new Cardinality();

	protected Cardinality()
	{
		super(Set.class, Integer.class);
	}

	@Override
	public Integer getValue(Set x)
	{
		return x.size();
	}
}
