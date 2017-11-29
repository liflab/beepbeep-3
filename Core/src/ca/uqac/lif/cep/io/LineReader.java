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

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.Queue;
import java.util.Scanner;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.tmf.Source;

/**
 * Source that reads text lines from a Java {@link InputStream}.
 * @author Sylvain Hallé
 */
public class LineReader extends Source
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 3187087342912223147L;

	/**
	 * The scanner to read from
	 */
	protected transient Scanner m_scanner;

	/**
	 * The input stream to read from
	 */
	protected transient InputStream m_inStream;

	/**
	 * Whether to add a carriage return at the end of each line
	 */
	protected boolean m_addCrlf = true;
	
	/**
	 * The character used as the CRLF on this system
	 */
	protected static final transient String CRLF = System.getProperty("line.separator");

	/**
	 * Creates a new LineReader from a File
	 * @param f The file to read from
	 * @throws FileNotFoundException If file is not found
	 */
	public LineReader(File f) throws FileNotFoundException
	{
		this(new FileInputStream(f));
	}

	/**
	 * Creates a new file reader from an input stream
	 * @param is The input stream to read from
	 */
	public LineReader(InputStream is)
	{
		super(1);
		m_inStream = is;
		m_scanner = new Scanner(is);
	}

	/**
	 * Tells the reader to add a carriage return at the end of each
	 * output event
	 * @param b true to add a CRLF, false otherwise
	 * @return This reader
	 */
	public LineReader addCrlf(boolean b)
	{
		m_addCrlf = b;
		return this;
	}

	@Override
	@SuppressWarnings("squid:S1168")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		if (m_scanner.hasNextLine())
		{
			String line = m_scanner.nextLine();
			if (m_addCrlf)
			{
				line += CRLF;
			}
			outputs.add(new Object[]{line});
			return true;
		}
		return false;
	}

	@Override
	public Processor duplicate()
	{
		return new LineReader(m_inStream);
	}
}
