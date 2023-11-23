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
package ca.uqac.lif.cep.io;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.Queue;
import java.util.Scanner;

/**
 * Source that reads text lines from a Java {@link InputStream}. It is represented
 * graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/io/ReadLines.png" alt="ReadLines">
 * 
 * @author Sylvain Hallé
 * @since 0.3
 */
@SuppressWarnings("squid:S2160")
public class ReadLines extends ReadTokens
{
	/**
	 * The scanner used to read lines from the file.
	 */
	protected final Scanner m_scanner;
	
	/**
   * Whether to add a carriage return at the end of each line
   */
  protected boolean m_addCrlf = false;

  /**
   * Whether to trim each text line from leading and trailing spaces
   */
  protected boolean m_trim = false;
	
	/**
	 * Creates a new file reader from an input stream
	 * 
	 * @param is
	 *          The input stream to read from
	 */
	public ReadLines(InputStream is)
	{
		super(is, null);
		m_scanner = new Scanner(is);
	}

	/**
	 * Creates a new file reader from an input stream
	 * 
	 * @param f The file to read from
	 * @throws FileNotFoundException Thrown if the file does not exist
	 */
	public ReadLines(File f) throws FileNotFoundException
	{
		this(new FileInputStream(f));
	}

	@Override
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
				line += ReadTokens.CRLF;
			}
			outputs.add(new Object[] {line});
			return true;
		}
		return false;
	}
}