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
package ca.uqac.lif.cep.numbers;

import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Converts an object into a number
 * @author Sylvain Hallé
 */
public class NumberCast extends UnaryFunction<Object,Number>
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = -7200217647590938462L;
	
	public static final transient NumberCast instance = new NumberCast();

	protected NumberCast()
	{
		super(Object.class, Number.class);
	}

	@Override
	public Number getValue(Object x)
	{
		return getNumber(x);
	}

	@Override
	public NumberCast duplicate()
	{
		return this;
	}

	/**
	 * Converts an object into a number
	 * @param x The object
	 * @return A number
	 */
	public static Number getNumber(Object x)
	{
		if (x instanceof Number)
		{
			return (Number) x;
		}
		if (x instanceof String)
		{
			try
			{
				return Integer.parseInt((String) x);
			}
			catch (NumberFormatException e)
			{
				try
				{
					return Float.parseFloat((String) x);
				}
				catch (NumberFormatException e2)
				{
					throw new FunctionException(e2);
				}
			}
		}
		throw new FunctionException("Object incompatible with Number");
	}
}
