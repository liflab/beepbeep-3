/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2023 Sylvain Hallé

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

import ca.uqac.lif.cep.UniformProcessor;

/**
 * Receives a stream of {@link Function} objects and applies these functions to
 * update an internal object kept in memory.
 * <p>
 * For example, suppose that the processor &pi; is instantiated with the value
 * 0 as its internal object. Let <i>f</i><sub>1</sub> be the function defined
 * as <i>f</i><sub>1</sub>(<i>x</i>) = <i>x</i>+1. Then pushing
 * <i>f</i><sub>1</sub> to &pi; produces the output event 1.
 * The processor receives <i>f</i><sub>1</sub>, evaluates it on its
 * internal object (0), and returns the result. Pushing <i>f</i><sub>1</sub>
 * once more will produce the output event 2.
 * @author Sylvain Hallé
 * @since 0.11.1
 */
public class Integrate extends UniformProcessor
{
	/**
	 * The start value of the internal object. It is retained in case the
	 * processor needs to be duplicated.
	 */
	/*@ non_null @*/ protected final Object m_start;
	
	/**
	 * The current value of the internal object. This object is replaced by a
	 * new one (or somehow "updated") on each input event received by the
	 * processor.
	 */
	protected Object m_current;
	
	/**
	 * Creates a new instance of the integrate processor.
	 * @param start The start value of the internal object
	 */
	public Integrate(Object start)
	{
		super(1, 1);
		m_start = start;
		m_current = start;
	}

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs)
	{
		Function f = (Function) inputs[0];
		Object[] f_out = new Object[1];
		f.evaluate(new Object[] {m_current}, f_out);
		outputs[0] = f_out[0];
		return true;
	}

	@Override
	public Integrate duplicate(boolean with_state)
	{
		Integrate in = new Integrate(m_start);
		if (with_state)
		{
			in.m_current = m_current;
		}
		return in;
	}
	
	@Override
	public String toString()
	{
		return "\u222b";
	}
}
