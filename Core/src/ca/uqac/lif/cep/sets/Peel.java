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

import java.util.Collection;

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * If the input is a singleton, extracts the element of that singleton.
 * In all other cases, returns the input as is.
 * @author Sylvain Hallé
 */
public class Peel extends UnaryFunction<Object,Object>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -3131574650958399872L;
	/**
	 * An instance of the peel function
	 */
	public static final transient Peel instance = new Peel();

	private Peel()
	{
		super(Object.class, Object.class);
	}

	@SuppressWarnings({"rawtypes", "squid:S1751"})
	@Override
	public Object getValue(Object x)
	{
		if (x instanceof Collection)
		{
			for (Object o : (Collection) x)
			{
				return o;
			}
		}
		return x;
	}
}
