/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.util.AnsiPrinter;

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
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		if (inputs == null || inputs.isEmpty())
		{
			return null;
		}
		Object o = inputs.firstElement();
		if (o != null)
		{
			m_out.setForegroundColor(AnsiPrinter.Color.LIGHT_GRAY);
			prettyPrint(o);
			m_out.setForegroundColor(AnsiPrinter.Color.RED);
			m_out.print(",");
		}
		return wrapVector(new Vector<Object>());
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		Processor p = (Processor) stack.pop();
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
	}
	
	protected void prettyPrint(Number n)
	{
		if (n.intValue() == n.floatValue())
		{
			m_out.print(n.intValue());
		}
	}
}
