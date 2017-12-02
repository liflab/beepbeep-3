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

import java.io.InputStream;

import ca.uqac.lif.cep.tmf.Source;

/**
 * Read contents from a Java {@link InputStream}.
 * @author Sylvain Hallé
 */
public abstract class ReadInputStream extends Source
{
	/**
	 * The input stream this processor is reading from
	 */
	protected InputStream m_inputStream;
	
	/**
	 * Creates a new input stream processor
	 * @param is The input stream to read from
	 */
	public ReadInputStream(InputStream is)
	{
		super(1);
		m_inputStream = is;
	}
	
	/**
	 * Character indicating the closing of a pipe.
	 * By default, we use ASCII 4, which is traditionally interpreted
	 * as the <a href="http://en.wikipedia.org/wiki/End-of-transmission_character">end
	 * of transmission character (EOT)</a>. This has no effect when the
	 * underlying input is not a pipe.
	 */
	public static final transient String END_CHARACTER = String.valueOf((char) 4);
	
	/**
	 * The size of chunks. The processor will try to read this number
	 * of bytes every time it queries the underlying input stream.
	 * Setting it to a too small value will cause the reader to loop
	 * uselessly to process tiny bits of the string. Setting it to a
	 * too large value (i.e. 1 MB) has an equally adverse effect.
	 * Experimentally, a sweet spot seems to be 16 kB.
	 */
	protected int m_chunkSize = 16384;
	
	/**
	 * Whether the input stream to read is connected to a file. This
	 * matters when attempting to read from the stream fails. If the
	 * source is a file, this means the file is over. Otherwise, it
	 * simply means there is no data ready to be read right now.
	 */
	protected boolean m_isFile = false;
	
	/**
	 * Whether the EOT character has been received
	 */
	protected boolean m_hasReadEot = false;
	
	/**
	 * Sets the size of chunks (in bytes) that the stream reader will try to
	 * read from the source at each attempt.
	 * @param size The size, in bytes. Must be greater than 0.
	 * @return This stream reader
	 */
	public ReadInputStream setChunkSize(int size)
	{
		m_chunkSize = size;
		return this;
	}
	
	/**
	 * Tells this reader whether it is reading from a file or some other
	 * input source. 
	 * @param b Set to {@code true} to tell the reader it is reading a
	 *   file, {@code false} otherwise
	 * @return This stream reader
	 */
	public ReadInputStream setIsFile(boolean b)
	{
		m_isFile = b;
		return this;
	}
	
	@Override
	public ReadInputStream duplicate()
	{
		// By default, it does not make sense to duplicate such a processor
		throw new UnsupportedOperationException();
	}
}
