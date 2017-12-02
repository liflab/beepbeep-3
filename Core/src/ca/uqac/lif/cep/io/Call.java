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
package ca.uqac.lif.cep.io;

import java.io.IOException;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.UniformProcessor;

/**
 * Processor calling an external command upon receiving an event,
 * and returning the output of that command as its output stream.
 * 
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class Call extends UniformProcessor
{
	/**
	 * The command to call
	 */
	protected final String[] m_command;

	public Call(String ... command)
	{
		super(1, 1);
		m_command = command;
	}

	/**
	 * The time to wait (in milliseconds) before polling the command's result
	 */
	protected static long s_waitInterval = 100;

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs)
	{
		// Pass the event (as is) to the standard input of the command
		try
		{
			byte[] contents = CommandRunner.runAndGet(m_command, (byte[]) inputs[0]);
			outputs[0] = contents;
			return true;
		}
		catch (IOException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public Call duplicate()
	{
		return new Call(m_command);
	}
}
