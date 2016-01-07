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
package ca.uqac.lif.cep.epl;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Constant;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * Repeatedly outputs the first event it has received. <code>Freeze</code>
 * works a bit like {@link Constant}; however, while <code>Constant</code>
 * is given the event to output, <code>Freeze</code> waits for a first event,
 * outputs it, and then outputs that event whenever some new input comes in.
 * 
 * @author Sylvain Hallé
 *
 */
public class Freeze extends SingleProcessor
{
	protected Object[] m_output;
	
	public Freeze()
	{
		super(1, 1);
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_output = null;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		if (m_output == null)
		{
			m_output = inputs;
		}
		return wrapVector(m_output);
	}
	
	public static void build(Stack<Object> stack)
	{
		Processor p = (Processor) stack.pop();
		stack.pop(); // FREEZE
		Freeze out = new Freeze();
		Connector.connect(p, out);
		stack.push(out);
	}
}
