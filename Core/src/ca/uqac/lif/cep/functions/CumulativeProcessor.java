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

import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Connector.ConnectorException;

/**
 * Creates a cumulative processor out of a cumulative function.
 * This is simply a {@link FunctionProcessor} whose function is of
 * a specific type (a {@link CumulativeFunction}). However, it has a
 * special grammar that allows any binary function to be turned into
 * a cumulative processor.
 */
public class CumulativeProcessor extends FunctionProcessor
{
	public CumulativeProcessor(CumulativeFunction<?> f)
	{	
		super(f);
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		Object o;
		Processor p;
		BinaryFunction<?,?,?> com = (BinaryFunction<?,?,?>) stack.pop();
		stack.pop(); // WITH
		o = stack.pop(); // ) ?
		if (o instanceof String)
		{
			p = Processor.liftProcessor(stack.pop());
			stack.pop(); // (
		}
		else
		{
			p = (Processor) o;
		}
		stack.pop(); // COMBINE
		@SuppressWarnings({ "rawtypes", "unchecked" })
		CumulativeFunction<?> func = new CumulativeFunction(com);
		CumulativeProcessor out = new CumulativeProcessor(func);
		Connector.connect(p, out);
		stack.push(out);
	}
}
