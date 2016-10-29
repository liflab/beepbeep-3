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
package ca.uqac.lif.cep.tmf;

import java.util.Stack;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.interpreter.Interpreter;

class NamedProcessorExpression extends ProcessorExpression
{
	public NamedProcessorExpression(Processor p, String n) 
	{
		super(p, n);
	}

	public static void build(Stack<Object> stack)
	{
		Object o;
		Processor p;
		String name;
		o = stack.pop(); // ) ?
		if (Interpreter.isSymbol(o, ")"))
		{
			name = (String) stack.pop();
			stack.pop(); // AS
			o = stack.pop(); // ) ?
			if (Interpreter.isSymbol(o, ")"))
			{
				// Case ((expression) AS name)
				stack.pop(); // AS
				p = (Processor) stack.pop();
				stack.pop(); // (
				stack.pop(); // (
			}
			else
			{
				// Case (expression AS name)
				p = (Processor) o;
				stack.pop(); // (
			}
		}
		else
		{
			name = (String) o;
			stack.pop(); // AS
			o = stack.pop(); // ) ?
			if (Interpreter.isSymbol(o, ")"))
			{
				// Case (expression) AS name
				p = (Processor) stack.pop();
				stack.pop(); // (
			}
			else
			{
				// Case expression AS name
				p = (Processor) o;
			}
		}
		// Phew!
		NamedProcessorExpression te = new NamedProcessorExpression(p, name);
		stack.push(te);
	}
}