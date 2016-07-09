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
package ca.uqac.lif.cep.cli;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.epl.Sink;
import ca.uqac.lif.cep.util.AnsiPrinter;

public class Print extends Sink
{
	/**
	 * The stream to print to
	 */
	protected AnsiPrinter m_out;
	
	public Print()
	{
		this(0, new AnsiPrinter(System.out));
	}
	
	public Print(int in_arity, AnsiPrinter out)
	{
		super(in_arity);
		m_out = out;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		if (inputs == null || allNull(inputs))
		{
			return null;
		}
		Object o = inputs[0];
		if (o != null)
		{
			m_out.setForegroundColor(AnsiPrinter.Color.LIGHT_GRAY);
			prettyPrint(o);
			m_out.setForegroundColor(AnsiPrinter.Color.RED);
			m_out.print(",");
		}
		return wrapVector(new Object[getOutputArity()]);
	}
	
	public static void build(Stack<Object> stack)
	{
		stack.pop(); // )
		Processor p = (Processor) stack.pop();
		stack.pop(); // (
		stack.pop(); // PRINT
		Print out = new Print(1, new AnsiPrinter(System.out));
		Connector.connect(p, out);
		stack.push(out);
	}
	
	protected void prettyPrint(Object o)
	{
		if (o instanceof Number)
		{
			prettyPrint((Number) o);
		}
		else
		{
			m_out.print(o);
		}
	}
	
	protected void prettyPrint(Number n)
	{
		if (n.intValue() == n.floatValue())
		{
			m_out.print(n.intValue());
		}
	}
	
	@Override
	public Print clone()
	{
		return new Print(getInputArity(), m_out);
	}
}
