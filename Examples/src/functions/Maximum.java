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

import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * Binary function that returns the maximum of two values.
 * 
 * @author Sylvain Hallé
 */
public class Maximum extends BinaryFunction<Number,Number,Number>
{
	/*
	 * This is optional. Since a Function object is stateless, the
	 * same instance can be used everywhere it is needed. Therefore,
	 * it is recommended to enforce the existence of a single instance
	 * by making the function's constructor private, and by making
	 * public a static field pointing to an instance of the function.
	 * By convention, you are encouraged to use the name "instance" for
	 * this field.
	 */
	public static final transient Maximum instance = new Maximum();

	private Maximum()
	{
		// The constructor should call super(), and pass the type of
		// the input arguments and the output
		super(Number.class, Number.class, Number.class);
	}

	@Override
	public Number getValue(Number x, Number y)
	{
		/*
		 * Method getValue() is where the output of the function is
		 * computed from the inputs.
		 */
		if (x.floatValue() > y.floatValue())
		{
			return x;
		}
		return y;
	}

	/*
	 * A small main method to illustrate the function
	 */
	public static void main(String[] args)
	{
		Maximum max = Maximum.instance;
		Object[] value;
		// A function is always called on an array of objects; this array
		// corresponds to the arguments. Here the function is unary, hence
		// the array is of size 2
		value = max.evaluate(new Float[]{3.5f, 10f});
		// Likewise, a function always returns an array of objects. Most
		// functions (like this one) return a single object, so the output
		// array is also of size 1
		System.out.printf("Return value of the function: %f\n", value[0]);
		value = max.evaluate(new Float[]{13.1f, 7.7f});
		System.out.printf("Return value of the function: %f\n", value[0]);
	}
}
