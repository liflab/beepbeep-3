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

import java.util.ArrayDeque;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * Computes the difference of its arguments
 * @author Sylvain Hallé
 */
public class Subtraction extends BinaryFunction<Number,Number,Number>
{
	/**
	 * Static reference to a single instance of the function
	 */
	public static final transient Subtraction instance = new Subtraction();

	private Subtraction()
	{
		super(Number.class, Number.class, Number.class);
	}

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		BinaryFunction.buildInfix(stack, instance);
	}

	@Override
	public Number getValue(Number x, Number y)
	{
		return x.floatValue() - y.floatValue();
	}

	@Override
	public Number getStartValue()
	{
		return 0;
	}

	@Override
	public String toString()
	{
		return "-";
	}

}
