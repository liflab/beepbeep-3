/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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
package ca.uqac.lif.cep;

import java.util.Queue;

/**
 * Processor that produces exactly one output front for each input
 * front received.
 * 
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public abstract class UniformProcessor extends SingleProcessor
{
	/**
	 * An array that will be used by the processor to compute
	 * its output
	 */
	protected transient Object[] m_outputArray;
	
	/**
	 * Creates a new uniform processor
	 * @param in_arity The input arity
	 * @param out_arity The output arity
	 */
	public UniformProcessor(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_outputArray = new Object[out_arity];
	}

	@Override
	protected final boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		boolean b = compute(inputs, m_outputArray);
		outputs.add(m_outputArray);
		return b;
	}

	@Override
	protected final boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException {
		Object[] outs = new Object[getOutputArity()];
		boolean b = onEndOfTrace(outs);
		if(b)
			outputs.add(outs);
		return b;
	}

	/**
	 * Computes one output events from its input events
	 * @param inputs An array of input events; its length corresponds to the
	 *   processor's input arity
	 * @param outputs An array where the outputs are produced
	 * @return A queue of vectors of output events, or null
	 *   if no event could be produced
	 */
	protected abstract boolean compute(Object[] inputs, Object[] outputs);

	/**
	 * Allows to describe a specific behavior when the trace of input fronts has reached its end.
	 * Called in "push mode" only. In "pull mode", implementing such a behavior can be done by using
	 * {@link Pullable#hasNext()} or {@link Pullable#hasNextSoft()}.
	 *
	 * @param outputs An array where the outputs are produced
	 * @return true if the processor should output one or several output fronts, false otherwise
	 *   and by default.
	 * @throws ProcessorException
	 */
	protected boolean onEndOfTrace(Object[] outputs) {
		return false;
	}

}
