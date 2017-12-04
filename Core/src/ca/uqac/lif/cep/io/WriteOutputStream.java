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
import java.io.OutputStream;
import java.util.Queue;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.tmf.Sink;

/**
 * Processor that writes events to a Java {@link OutputStream}.
 * @author Sylvain Hallé
 */
public class WriteOutputStream extends Sink 
{
	/**
	 * The output stream to send data to
	 */
	protected transient OutputStream m_outputStream;

	/**
	 * Creates a new output stream processor
	 * @param os The output stream to send data to
	 */
	public WriteOutputStream(OutputStream os)
	{
		super(1);
		m_outputStream = os;
	}

	@Override
	@SuppressWarnings({"squid:S1168", "squid:S3516"})
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		try
		{
			append(inputs[0]);
			return false;
		}
		catch (IOException e)
		{
			throw new ProcessorException(e);
		}
		catch (UnsupportedOperationException e)
		{
			throw new ProcessorException(e);
		}
	}

	/**
	 * Writes a new object to the output stream.
	 * @param o The object to write to the output stream. Can either be
	 * a byte array or a string. Any other kind of object will throw an
	 * exception.
	 * @throws IOException If writing to the output stream cannot be done
	 */
	protected void append(Object o) throws IOException
	{
		if (o instanceof byte[])
		{
			m_outputStream.write((byte[]) o);
		}
		else if (o instanceof String)
		{
			m_outputStream.write(((String) o).getBytes());
		}
		else
		{
			throw new UnsupportedOperationException("Cannot write this object to an output stream");
		}
	}

	@Override
	public WriteOutputStream duplicate()
	{
		// By default, it does not make sense to duplicate such a processor
		throw new UnsupportedOperationException();
	}
}
