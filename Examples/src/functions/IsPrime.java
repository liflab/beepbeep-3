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

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Unary function that checks if a number is prime.
 * 
 * @author Sylvain Hallé
 */
public class IsPrime extends UnaryFunction<Number,Boolean> 
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
	public static final transient IsPrime instance = new IsPrime();

	private IsPrime()
	{
		// The constructor should call super(), and pass the type of
		// the input and output
		super(Number.class, Boolean.class);
	}

	@Override
	public Boolean getValue(Number x) 
	{
		/*
		 * Method getValue() is where the output of the function is
		 * computed for the input. For the sake of our example, the
		 * actual way to check if x is prime does not matter;
		 * we'll simply enumerate all numbers up to sqrt(x) until we 
		 * find one that divides x, and otherwise return true. 
		 */
		int k = x.intValue(); // Convert x to an int
		int max = (int) Math.sqrt(k);
		for (int n = 2; n <= max; n++)
		{
			if (k % n == 0)
				return false; // Found a divisor: x is not prime
		}
		return true;
	}
	
	/*
	 * A small main method to illustrate the function
	 */
	public static void main(String[] args)
	{
		IsPrime ip = IsPrime.instance;
		Object[] value;
		// A function is always called on an array of objects; this array
		// corresponds to the arguments. Here the function is unary, hence
		// the array is of size 1
		value = ip.evaluate(new Integer[]{3});
		// Likewise, a function always returns an array of objects. Most
		// function (like this one) returns a single object, so the output
		// array is also of size 1
		System.out.printf("Return value of the function: %b\n", value[0]);
		value = ip.evaluate(new Integer[]{8});
		System.out.printf("Return value of the function: %b\n", value[0]);
	}
}
