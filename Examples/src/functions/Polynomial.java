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

import ca.uqac.lif.cep.functions.ArgumentPlaceholder;
import ca.uqac.lif.cep.functions.ConstantFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.functions.PassthroughFunction;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.numbers.Multiplication;

/**
 * Create a {@link ca.uqac.lif.cep.functions.PassthroughFunction} object from
 * an instance of {@link ca.uqac.lif.cep.functions.FunctionTree}.
 * 
 * @author Sylvain Hallé
 */
public class Polynomial extends PassthroughFunction 
{
	/*
	 * We need to implement the getFunction() method, which must
	 * return an object of type Function. Here, we create a FunctionTree
	 * that computes x^2+3.
	 */
	@Override
	public Function getFunction() 
	{
		return new FunctionTree(Addition.instance,
				new FunctionTree(Multiplication.instance,
						new ArgumentPlaceholder(),
						new ArgumentPlaceholder()),
				new ConstantFunction(3));
	}

	/*
	 * Small main() to illustrate the concept
	 */
	public static void main(String[] args) 
	{
		Polynomial poly = new Polynomial();
		Object[] value;
		value = poly.evaluate(new Integer[]{3});
		System.out.printf("Return value of the function: %f\n", value[0]);
		value = poly.evaluate(new Integer[]{8});
		System.out.printf("Return value of the function: %f\n", value[0]);
	}
}
