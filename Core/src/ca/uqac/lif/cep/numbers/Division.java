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

import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionTree;

public class Division extends BinaryFunction<Number,Number,Number>
{
	/**
	 * Static reference to a single instance of the function
	 */
	public static final transient Division instance = new Division();
	
	private Division()
	{
		super(Number.class, Number.class, Number.class);
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException
	{
		stack.pop(); // (
		Function right = (Function) stack.pop();
		stack.pop(); // )
		stack.pop(); // symbol
		stack.pop(); // (
		Function left = (Function) stack.pop();
		stack.pop(); // )
		FunctionTree ft = new FunctionTree(instance, left, right);
		stack.push(ft);
	}

	@Override
	public Number getValue(Number x, Number y) 
	{
		return x.floatValue() / y.floatValue();
	}

	@Override
	public Number getStartValue() 
	{
		return 1;
	}
	
	@Override
	public String toString()
	{
		return "÷";
	}
}
