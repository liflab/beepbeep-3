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

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.PullableException;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * Receives input events and stores them. As its name implies, the
 * <code>Sink</code> is just that: the end of a pipe of processors where
 * events are input, but which has no output. In other words, a sink
 * is a processor with an output arity of 0.
 * <p>
 * When operating in "pull" mode, it is nevertheless possible to ask the
 * sink to pull on its inputs; this is why, like a {@link Pullable}, it
 * implements methods {@link #pull()} and {@link #pullHard()}.
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public abstract class Sink extends SingleProcessor
{
	public Sink()
	{
		this(1);
	}

	public Sink(int in_arity)
	{
		super(in_arity, 0);
	}

	/**
	 * Tells the sink to pull events from the pipeline
	 */
	public final void pull()
	{
		Object[] inputs = new Object[getInputArity()];
		for (int i = 0; i < getInputArity(); i++)
		{
			Pullable p = m_inputPullables[i];
			inputs[i] = p.pullSoft();
		}
		try
		{
			compute(inputs, null);
		}
		catch (ProcessorException e)
		{
			throw new PullableException(e);
		}
	}

	/**
	 * Tells the sink to pull events from the pipeline
	 */
	public final void pullHard()
	{
		Object[] inputs = new Object[getInputArity()];
		for (int i = 0; i < getInputArity(); i++)
		{
			Pullable p = m_inputPullables[i];
			inputs[i] = p.pull();
		}
		try
		{
			compute(inputs, null);
		}
		catch (ProcessorException e)
		{
			throw new PullableException(e);
		}
	}	
}
