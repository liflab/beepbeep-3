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

import java.util.ArrayDeque;
import java.util.Queue;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Pushable.PushableException;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * Produces output events from no input. In other words, a source is a
 * processor with input arity 0. It is the opposite of the {@link Sink}.
 * <p>
 * While a source has no input <em>trace</em>, this does not mean it has
 * not input at all. For example, a processor reading from a file and creating
 * events out of the file's content is an example of a source. It does not
 * receive events as input, yet creates output events from something external
 * to it.
 * 
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public abstract class Source extends SingleProcessor
{
	public Source(int out_arity)
	{
		super(0, out_arity);
	}

	/**
	 * Tells the source to push events into the pipeline
	 */
	public final void push()
	{
		Queue<Object[]> output = new ArrayDeque<Object[]>(1);
		try
		{
			compute(null, output);
		}
		catch (ProcessorException e)
		{
			throw new PushableException(e);
		}
		if (output.isEmpty())
		{
			return;
		}
		for (Object[] evt : output)
		{
			if (evt != null && !allNull(evt))
			{
				for (int i = 0; i < output.size(); i++)
				{
					Pushable p = m_outputPushables[i];
					p.push(evt[i]);
				}
				for (int i = 0; i < output.size(); i++)
				{
					m_outputPushables[i].waitFor();
				}
			}
		}
	}
}
