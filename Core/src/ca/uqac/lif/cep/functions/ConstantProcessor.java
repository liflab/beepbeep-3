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
package ca.uqac.lif.cep.functions;

import java.util.ArrayDeque;

/**
 * Function processor returning a constant value.
 * This processor exists only to facilitate the creation of constant
 * processors in ESQL. If you want to create a constant processor
 * programmatically, then both of these two calls amount to the
 * same thing:
 * <pre>
 * x = new FunctionProcessor(new Constant(foo));
 * x = new ConstantProcessor(foo);
 * </pre>
 * 
 * @author Sylvain Hallé
 */
public class ConstantProcessor extends FunctionProcessor
{
	public ConstantProcessor(Constant comp)
	{
		super(comp);
	}

	public static void build(ArrayDeque<Object> stack)
	{
		Object o;
		Constant c;
		o = stack.pop(); // ( ?
		if (o instanceof String && o.toString().compareTo("(") == 0)
		{
			c = (Constant) stack.pop();
			stack.pop(); // )
		}
		else
		{
			c = (Constant) o;
		}
		stack.pop(); // CONSTANT
		FunctionProcessor fp = new FunctionProcessor(c);
		stack.push(fp);
	}
}
