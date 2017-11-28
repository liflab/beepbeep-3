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
 * Adds all the elements of the second multiset to the first, and
 * returns this first multiset as its output. This function <em>modifies</em>
 * the first multiset and returns it. This should be contrasted with
 * {@link MultisetUnion}.
 * 
 * @author Sylvain Hallé
 */
public class MultisetAddAll extends BinaryFunction<Multiset,Multiset,Multiset>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 7357759815129981048L;
	/**
	 * A static instance of the function
	 */
	public static final transient MultisetAddAll instance = new MultisetAddAll();

	private MultisetAddAll()
	{
		super(Multiset.class, Multiset.class, Multiset.class);
	}

	@Override
	public Multiset getValue(Multiset x, Multiset y)
	{
		x.addAll(y);
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
