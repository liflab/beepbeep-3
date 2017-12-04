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
package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.UniformProcessor;

/**
 * Repeatedly outputs the first event it has received. <code>Freeze</code>
 * works a bit like {@link PullConstant}; however, while <code>Constant</code>
 * is given the event to output, <code>Freeze</code> waits for a first event,
 * outputs it, and then outputs that event whenever some new input comes in.
 * 
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class Freeze extends UniformProcessor
{
	/**
	 * The event front to freeze
	 */
	protected transient Object[] m_output;

	/**
	 * Creates a new freeze processor
	 */
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
	protected boolean compute(Object[] inputs, Object[] outputs)
	{
		if (m_output == null)
		{
			m_output = inputs;
		}
		outputs[0] = m_output[0];
		return true;
	}

	@Override
	public Freeze duplicate()
	{
		return new Freeze();
	}
}
