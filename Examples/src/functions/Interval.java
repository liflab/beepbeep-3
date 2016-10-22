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

import ca.uqac.lif.cep.functions.And;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.functions.ArgumentPlaceholder;
import ca.uqac.lif.cep.numbers.IsGreaterThan;
import ca.uqac.lif.cep.numbers.IsLessThan;

/**
 * Creates a compound function (i.e. a
 * {@link ca.uqac.lif.cep.functions.FunctionTree})
 * that checks if a number lies between two
 * other numbers.
 * @author Sylvain Hallé
 *
 */
public class Interval 
{
	public static void main(String[] args)
	{
		/*
		 * A FunctionTree is a function object created by
		 * composing multiple functions together. Here we create
		 * a function f(x,y,z) that returns true if x lies between
		 * y and z. The TracePlaceholder objects are used to
		 * refer to the arguments, with the first argument starting at 0.
		 */
		// SNIP
		FunctionTree in_interval = new FunctionTree(And.instance,
				new FunctionTree(IsGreaterThan.instance, 
						new ArgumentPlaceholder(0),
						new ArgumentPlaceholder(1)), // x > y
				new FunctionTree(IsLessThan.instance,
						new ArgumentPlaceholder(0),
						new ArgumentPlaceholder(2) // y < z
						));
		// SNIP
		Object[] value;
		value = in_interval.evaluate(new Integer[]{3, 2, 8});
		// Likewise, a function always returns an array of objects. Most
		// functions (like this one) return a single object, so the output
		// array is also of size 1
		System.out.printf("Return value of the function: %b\n", value[0]);
		value = in_interval.evaluate(new Integer[]{6, 7, 9});
		System.out.printf("Return value of the function: %b\n", value[0]);
	}
}
