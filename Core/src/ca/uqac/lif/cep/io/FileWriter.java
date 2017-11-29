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
package ca.uqac.lif.cep.io;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Queue;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.tmf.Sink;

/**
 * Writes events to a file on disk
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class FileWriter extends Sink
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -2468469352121292509L;

	/**
	 * The output stream to which contents will be written
	 */
	private FileOutputStream m_outStream;

	/**
	 * The file to which the contents will be written
	 */
	private final File m_file;

	/**
	 * Whether the contents of each new event are to be appended to
	 * the file, or should overwrite the previous contents
	 */
	private final boolean m_append;

	/**
	 * Instantiates a file writer
	 * @param file The file to write to
	 * @param append Set to <code>true</code> to append contents of
	 *   each event; otherwise each new event will overwrite the previous
	 *   one in the file
	 */
	public FileWriter(File file, boolean append)
	{
		super(1);
		m_file = file;
		m_append = append;
	}

	@Override
	@SuppressWarnings({"squid:S1168", "squid:S3516"})
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) throws ProcessorException
	{
		// We return false everywhere, since anyway the FileWriter is
		// a sink, so we'll never call pull on it
		if (inputs == null || inputs[0] == null)
		{
			// Don't write anything if the input is null
			return false;
		}
		try
		{
			if (m_append)
			{
				append(inputs[0]);
				return false;
			}
			overwrite(inputs[0]);
		}
		catch (IOException e)
		{
			throw new ProcessorException(e);
		}
		return false;
	}

	private void overwrite(Object o) throws IOException
	{
		m_outStream = new FileOutputStream(m_file);
		append(o);
		m_outStream.close();
	}

	private void append(Object o) throws IOException
	{
		if (o instanceof byte[])
		{
			m_outStream.write((byte[]) o);
		}
		if (o instanceof String)
		{
			m_outStream.write(((String) o).getBytes());
		}
	}

	/**
	 * Closes the file linked to this file writer
	 * @return A reference to the current file writer
	 */
	public FileWriter close() throws IOException
	{
		m_outStream.close();
		return this;
	}

	@Override
	public FileWriter duplicate()
	{
		return new FileWriter(m_file, m_append);
	}
}
