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
package ca.uqac.lif.cep.cli;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

/**
 * Scans characters from an input stream. This class is only used
 * by the main loop of {@link CommandLine}.
 * 
 * @author Sylvain Hallé
 */
class CharScanner
{
	protected InputStream m_is;

	protected volatile boolean m_exit;

	public CharScanner(InputStream is)
	{
		super();
		m_is = is;
	}

	public char nextChar()
	{
		InputStreamReader reader = new InputStreamReader(m_is);
		m_exit = false;
		while(!m_exit)
		{
			try
			{
				if (reader.ready())
				{
					// read a character and process it
					return (char) reader.read();
				}
			}
			catch (IOException e)
			{
				// Do nothing
			}
			// Let's not hog any cpu time
			try
			{
				Thread.sleep(50);
			}
			catch (InterruptedException ex)
			{
				// can't do much about it can we? Ignoring
				Thread.currentThread().interrupt();
			}
		}
		return (char) 0;
	}
}