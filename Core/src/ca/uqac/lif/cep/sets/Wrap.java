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

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Wraps the input into a multiset.
 * @author Sylvain Hallé
 */
public class Wrap extends UnaryFunction<Object,Multiset>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -592164180067579744L;
	/**
	 * An instance of the peel function
	 */
	public static final transient Wrap instance = new Wrap();

	private Wrap()
	{
		super(Object.class, Multiset.class);
	}

	@Override
	public Multiset getValue(Object x)
	{
		Multiset set = new Multiset();
		set.add(x);
		return set;
	}

	@Override
	public String toString()
	{
		return "wrap";
	}
}
