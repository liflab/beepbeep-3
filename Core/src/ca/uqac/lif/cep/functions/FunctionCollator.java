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

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.tmf.Collator;

/**
 * Applies a function to a input events from one or more traces.
 * This processor must work in tandem with the 
 * {@link ca.uqac.lif.tmf.Collator Collator}: its input is a
 * {@link ca.uqac.lif.util.CacheMap CacheMap} of input events
 * associated with names.
 * <p>
 * The usefulness of this processor lies mostly in the ESQL language.
 * It makes it possible to write something like:
 * <pre>
 * APPLY $A + $B WITH 
 *   expression AS $A, 
 *   expression AS $B
 * </pre>
 * <p>
 * If you want to apply a function to events programmatically (instead
 * of through ESQL), it is simpler to use a {@link FunctionProcessor}.
 * 
 * @author Sylvain Hallé
 */
public class FunctionCollator extends SingleProcessor 
{
	protected Function m_function;
	
	public FunctionCollator(Function f)
	{
		super(1, f.getOutputArity());
		m_function = f;
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException, ConnectorException
	{
		Object o;
		Function f;
		Collator col = (Collator) stack.pop();
		o = stack.pop(); // ) ?
		if (o instanceof String)
		{
			f = (Function) stack.pop();
			stack.pop(); // (
		}
		else
		{
			f = (Function) o;
		}
		stack.pop(); // APPLY
		FunctionCollator fp = new FunctionCollator(f);
		Connector.connect(col, fp);
		stack.push(fp);
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object[] outputs = m_function.evaluate(inputs);
		return wrapVector(outputs);
	}

	@Override
	public Processor clone()
	{
		return new FunctionCollator(m_function.clone(getContext()));
	}
}
