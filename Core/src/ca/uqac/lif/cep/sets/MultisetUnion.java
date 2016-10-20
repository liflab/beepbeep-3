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
 * Binary function taking as input two multisets, and returning as
 * its output a <em>new</em> multiset containing all elements of
 * both. This should be contrasted with {@link MultisetAddAll}.
 * 
 * @author Sylvain Hallé
 */
public class MultisetUnion extends BinaryFunction<Multiset,Multiset,Multiset> 
{
	/**
	 * A static instance of the function
	 */
	public static final transient MultisetUnion instance = new MultisetUnion();
	
	private MultisetUnion()
	{
		super(Multiset.class, Multiset.class, Multiset.class);
	}
	
	@Override
	public Multiset getValue(Multiset x, Multiset y) 
	{
		Multiset out = new Multiset();
		out.addAll(x);
		out.addAll(y);
		return out;
	}

	@Override
	public Multiset getStartValue() 
	{
		return new Multiset();
	}
	
	@Override
	public String toString()
	{
		return " U ";
	}
}
