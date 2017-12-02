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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Queue;

import ca.uqac.lif.cep.ProcessorException;

/**
 * Extracts character strings from a Java {@link InputStream}.
 * @author Sylvain Hallé
 */
public class ReadStringStream extends ReadInputStream 
{
	/**
	 * A reader to wrap around this input stream
	 */
	protected transient InputStreamReader m_inputStreamReader;

	/**
	 * A buffered reader to wrap around the input stream
	 */
	protected transient BufferedReader m_br;

	/**
	 * Creates a new stream reader
	 * @param is The input stream to read from
	 */
	public ReadStringStream(/*@NotNull*/ InputStream is)
	{
		super(is);
		m_inputStreamReader = new InputStreamReader(is);
		m_br = new BufferedReader(m_inputStreamReader);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
	{
		if (m_hasReadEot)
		{
			// We received EOT previously: no more output to produce
			return false;
		}
		try
		{
			if (m_br.ready())
			{
				char[] char_array = new char[m_chunkSize];
				int chars_read = m_br.read(char_array, 0, m_chunkSize);
				// When the input is a pipe and we read the special character,
				// this indicates the end of transmission
				if (chars_read > 0)
				{
					char[] new_array = Arrays.copyOf(char_array, chars_read);
					String st = new String(new_array);
					if (!m_isFile && st.endsWith(END_CHARACTER))
					{
						// We don't read a file, but the input stream
						// has the EOT character: trim this EOT form the output
						st = st.substring(0,  st.length() - 1);
						// And remember this stream is over
						m_hasReadEot = true;
					}
					outputs.add(new Object[]{st});
					return true;
				}
			}
			else
			{
				// If the underlying input source is not a pipe, the
				// fact that the input stream is not ready means there
				// is no more data to read.
				if (m_isFile)
				{
					return false;
				}
			}
			// At this point, we haven't read bytes, but we don't know if we'll
			// be able to read some in the future: return true just in case
			return true;
		}
		catch (IOException e)
		{
			throw new ProcessorException(e);
		}
	}
}
