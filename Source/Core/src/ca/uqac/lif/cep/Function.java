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

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

public class Function extends SingleProcessor
{
	/**
	 * The object responsible for the computation
	 */
	protected final Computable m_compute;
	
	public Function()
	{
		super();
		m_compute = null;
	}
	
	public Function(Computable comp)
	{
		super(comp.getInputArity(), comp.getOutputArity());
		m_compute = comp;
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		return wrapVector(m_compute.compute(inputs));
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		// Principle: pop processors from the stack and count them,
		// until we pop the Computable. The computable tells us how
		// many processors we need to pop based on its input arity. This
		// way, we can deal with prefix n-ary and infix binary functions
		// at the same time.
		List<Processor> inputs = new LinkedList<Processor>();
		int num_popped = 0;
		int arity = Computable.s_maxInputArity;
		Computable c = null;
		do
		{
			Object o = stack.pop();
			if (o instanceof Processor)
			{
				num_popped++;
				inputs.add((Processor) o);
			}
			else if (o instanceof Computable)
			{
				c = (Computable) o;
				arity = c.getInputArity();
			}
			else
			{
				// This should not happen
				assert false;
			}
		} while (num_popped < arity);
		// Instantiate the processor and connect it to its input traces
		Function out = new Function(c);
		for (int i = 0; i < inputs.size(); i++)
		{
			Processor p = inputs.get(i);
			Connector.connect(p, out, 0, i);
		}
		stack.push(out);
	}
}
