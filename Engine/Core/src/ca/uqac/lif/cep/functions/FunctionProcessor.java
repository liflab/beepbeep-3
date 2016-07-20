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

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.Connector.ConnectorException;

/**
 * Applies a function to input events to produce output events. This 
 * class provides a way to "lift" any <i>m</i>-to-<i>n</i> function
 * into an <i>m</i>-to-<i>n</i> processor, by simply calling the
 * function on the inputs to produce the outputs.
 * 
 * @author Sylvain Hallé
 *
 */
public class FunctionProcessor extends SingleProcessor
{
	/**
	 * The object responsible for the computation
	 */
	protected final Function m_function;
	
	/**
	 * Instantiates a new function processor
	 * @param comp The computable object responsible for the computation
	 */
	public FunctionProcessor(Function comp)
	{
		super(comp.getInputArity(), comp.getOutputArity());
		m_function = comp;
	}
	
	@Override
	public void reset()
	{
		m_function.reset();
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		return wrapVector(m_function.evaluate(inputs, m_context));
	}
	
	@Override
	public FunctionProcessor clone()
	{
		FunctionProcessor out = new FunctionProcessor(m_function.clone());
		return out;
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException, ConnectorException
	{
		// Principle: pop processors from the stack and count them,
		// until we pop the Computable. The computable tells us how
		// many processors we need to pop based on its input arity. This
		// way, we can deal with prefix n-ary and infix binary functions
		// at the same time.
		List<Processor> inputs = new LinkedList<Processor>();
		int num_popped = 0;
		int arity = Function.s_maxInputArity;
		Function c = null;
		do
		{
			Object o = stack.pop();
			if (o instanceof Processor)
			{
				num_popped++;
				inputs.add((Processor) o);
			}
			else if (o instanceof Function)
			{
				c = (Function) o;
				arity = c.getInputArity();
			}
			else
			{
				// This should not happen
				assert false;
			}
		} while (num_popped < arity);
		// Instantiate the processor and connect it to its input traces
		FunctionProcessor out = new FunctionProcessor(c);
		for (int i = 0; i < inputs.size(); i++)
		{
			Processor p = inputs.get(i);
			Connector.connect(p, out, 0, i);
		}
		stack.push(out);
	}
	
	@Override
	public final void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
	{
		// The type is determined by that of the underlying function
		m_function.getInputTypesFor(classes, index);
	}
	
	@Override
	public final Class<?> getOutputTypeFor(int index)
	{
		// The type is determined by that of the underlying function
		return m_function.getOutputTypeFor(index);
	}

}
