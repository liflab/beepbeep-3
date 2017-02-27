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
package functions;

import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.numbers.Addition;

/**
 * Add two numbers with the {@link ca.uqac.lif.cep.numbers.Addition}
 * function.
 * @author Sylvain Hallé
 */
public class AddNumbers
{
	public static void main(String[] args)
	{
		// SNIP
		Function add = Addition.instance;
		Object[] inputs = new Object[]{2, 3};
		Object[] values = new Object[1];
		add.evaluate(inputs, values);
		float value = (Float) values[0]; // = 5
		// SNIP
		System.out.printf("The value is %f\n", value);
	}
}
