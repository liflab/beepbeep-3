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
package ca.uqac.lif.cep.numbers;

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Computes the square root of its argument
 * @author Sylvain Hallé
 */
public class SquareRoot extends UnaryFunction<Number,Number>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -858548415149836732L;
	/**
	 * A static instance of absolute value
	 */
	public static final transient SquareRoot instance = new SquareRoot();

	SquareRoot()
	{
		super(Number.class, Number.class);
	}

	@Override
	public Number getValue(Number x)
	{
		return Math.sqrt(x.floatValue());
	}

	@Override
	public String toString()
	{
		return "√";
	}

}
