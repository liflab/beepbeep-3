/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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
package ca.uqac.lif.cep.eml.numbers;

import java.util.Stack;

import ca.uqac.lif.cep.Combinable;

public class Sum implements Combinable
{
	public Sum()
	{
		super();
	}
	
	public static void build(Stack<Object> stack)
	{
		Sum out = new Sum();
		stack.push(out);
	}

	@Override
	public Object[] initialize()
	{
		Object[] ob = new Object[1];
		ob[0] = 0;
		return ob;
	}

	@Override
	public Object[] combine(Object[] inputs, Object[] total)
	{
		Object[] ob = new Object[1];
		Number n1 = (Number) total[0];
		Number n2 = (Number) inputs[0];
		Number n3 = n1.floatValue() + n2.floatValue();
		ob[0] = n3;
		return ob;
	}

	@Override
	public int getInputArity()
	{
		return 1;
	}

	@Override
	public int getOutputArity()
	{
		return 1;
	}

}
