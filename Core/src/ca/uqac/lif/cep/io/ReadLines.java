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

import java.io.BufferedInputStream;
import java.io.InputStream;
import java.util.Queue;
import java.util.Scanner;

/**
 * Source that reads text lines from a Java {@link InputStream}.
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2160")
public class ReadLines extends ReadInputStream
{
	/**
	 * The scanner to read from
	 */
	protected transient Scanner m_scanner;
	
	/**
	 * The buffered input stream to wrap
	 */
	protected transient BufferedInputStream m_bufferedInputStream;

	/**
	 * Whether to add a carriage return at the end of each line
	 */
	protected boolean m_addCrlf = false;
	
	/**
	 * Whether to trim each text line from leading and trailing spaces
	 */
	protected boolean m_trim = false;
	
	/**
	 * The character used as the CRLF on this system
	 */
	public static final transient String CRLF = System.getProperty("line.separator");

	/**
	 * Creates a new file reader from an input stream
	 * @param is The input stream to read from
	 */
	public ReadLines(InputStream is)
	{
		super(is);
		m_bufferedInputStream = new BufferedInputStream(is);
		m_scanner = new Scanner(m_bufferedInputStream);
	}

	/**
	 * Tells the reader to add a carriage return at the end of each
	 * output event
	 * @param b true to add a CRLF, false otherwise
	 * @return This reader
	 */
	public ReadLines addCrlf(boolean b)
	{
		m_addCrlf = b;
		return this;
	}
	
	/**
	 * Tells the reader to trim each text line
	 * @param b true to trim, false otherwise
	 * @return This reader
	 */
	public ReadLines trim(boolean b)
	{
		m_trim = b;
		return this;
	}

	@Override
	@SuppressWarnings("squid:S1168")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		if (m_scanner.hasNextLine())
		{
			String line = m_scanner.nextLine();
			if (m_trim)
			{
				line = line.trim();
			}
			if (m_addCrlf)
			{
				line += CRLF;
			}
			outputs.add(new Object[]{line});
			return true;
		}
		return false;
	}
}