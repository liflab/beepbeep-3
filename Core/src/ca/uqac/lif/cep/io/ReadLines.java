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
import java.io.FileNotFoundException;
import java.io.InputStream;

import ca.uqac.lif.cep.functions.ReadTokens;

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
	 * Creates a new file reader from an input stream
	 * 
	 * @param is
	 *          The input stream to read from
	 */
	public ReadLines(InputStream is)
	{
		super(is, CRLF);
	}

	/**
	 * Creates a new file reader from an input stream
	 * 
	 * @param f The file to read from
	 * @throws FileNotFoundException Thrown if the file does not exist
	 */
	public ReadLines(File f) throws FileNotFoundException
	{
		super(f, CRLF);
	}

	@Override
	public ReadLines addCrlf(boolean b)
	{
		super.addCrlf(b);
		return this;
	}

	@Override
	public ReadLines trim(boolean b)
	{
		super.trim(b);
		return this;
	}
}