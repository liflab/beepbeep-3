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

import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * Adds an element to a multiset. This function <em>modifies</em>
 * the multiset and returns it.
 * 
 * @author Sylvain Hallé
 */
public class MultisetAddElement extends BinaryFunction<Multiset,Object,Multiset>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 893561486871547176L;
	/**
	 * A static instance of the function
	 */
	public static final transient MultisetAddElement instance = new MultisetAddElement();

	private MultisetAddElement()
	{
		super(Multiset.class, Object.class, Multiset.class);
	}

	@Override
	public Multiset getValue(Multiset x, Object y)
	{
		x.add(y);
		return x;
	}

	@Override
	public Multiset getStartValue()
	{
		return new Multiset();
	}

	@Override
	public String toString()
	{
		return " += ";
	}
}
