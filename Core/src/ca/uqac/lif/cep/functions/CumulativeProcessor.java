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

import java.util.ArrayDeque;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.EventIndex;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.petitpoucet.DirectValue;
import ca.uqac.lif.petitpoucet.NodeFunction;

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

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs) throws ProcessorException
	{
		// We override compute() from FunctionProcessor, only to complete the
		// association between input and output events (each output event depends on
		// the current input event and also the previous output event front)
		boolean b = super.compute(inputs, outputs);
		if (m_eventTracker != null)
		{
			for (int j = 0; j < outputs.length; j++)
			{
				if (m_outputCount > 1)
				{
					for (int k = 0; k < outputs.length; k++)
					{
						// -1 and -2 since the count has already been incremented by the
						// call to super.compute() above
						associateToOutput(j, m_outputCount - 2, k, m_outputCount - 1);
					}
				}
				else
				{
					for (int k = 0; k < outputs.length; k++)
					{
						// -1 and -2 since the count has already been incremented by the
						// call to super.compute() above
						associateTo(new StartValue(getId(), j, m_outputCount - 1, new DirectValue()), k, m_outputCount - 1);
					}
				}
			}
		}
		return b;
	}

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
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

	public static class StartValue extends EventIndex
	{
		public StartValue(int id, int index, int position, NodeFunction dependency) 
		{
			super(id, index, position, new DirectValue());
		}

		@Override
		public String toString()
		{
			return "Start value";
		}
	}
}
