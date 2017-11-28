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

import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * Computes the sum of its arguments
 * @author Sylvain Hallé
 */
public class Addition extends BinaryFunction<Number,Number,Number>
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = -7410938141238455733L;
	
	/**
	 * A static instance of addition
	 */
	public static final transient Addition instance = new Addition();

	/**
	 * Make constructor private, to force users to refer to the static
	 * instance of addition
	 */
	protected Addition()
	{
		super(Number.class, Number.class, Number.class);
	}

	@Override
	public Number getValue(Number x, Number y)
	{
		return x.floatValue() + y.floatValue();
	}

	@Override
	public Number getStartValue()
	{
		return 0f;
	}

	@Override
	public String toString()
	{
		return "+";
	}
}
