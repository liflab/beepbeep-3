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
import java.util.ArrayDeque;
import java.util.Queue;

/**
 * Separates a stream of string chunks into tokens according to a user-defined
 * separator.
 * 
 * @author Sylvain Hallé
 * @since 0.11.1
 */
@SuppressWarnings("squid:S2160")
public class ReadTokens extends ReadStringStream
{
  /**
   * The character used as the CRLF on this system
   */
  public static final transient String CRLF = System.getProperty("line.separator");
  
  /**
   * The separator used to delimitate tokens.
   */
  protected final String m_separator;
  
  /**
   * The line chunk that awaits for its line separator.
   */
  protected String m_lastChunk = "";

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
   * @param is The input stream to read from
   * @param separator The separator used to delimitate tokens
   */
  public ReadTokens(InputStream is, String separator)
  {
    super(is);
    m_separator = separator;
  }

  /**
   * Creates a new file reader from a file
   * 
   * @param f The file to read from
   * @param separator The separator used to delimitate tokens
   */
  public ReadTokens(File f, String separator) throws FileNotFoundException
  {
    super(f);
    m_separator = separator;
  }
  
  /**
   * Tells the reader to add a carriage return at the end of each output event
   * 
   * @param b
   *          true to add a CRLF, false otherwise
   * @return This reader
   */
  public ReadTokens addCrlf(boolean b)
  {
    m_addCrlf = b;
    return this;
  }

  /**
   * Tells the reader to trim each text line
   * 
   * @param b
   *          true to trim, false otherwise
   * @return This reader
   */
  public ReadTokens trim(boolean b)
  {
    m_trim = b;
    return this;
  }
  
  @Override
  @SuppressWarnings("squid:S1168")
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    Queue<Object[]> q = new ArrayDeque<Object[]>(1);
    boolean b = super.compute(inputs, q);
    if (!b && !m_lastChunk.isEmpty())
    {
      prepareChunk(m_lastChunk, outputs);
      m_lastChunk = "";
      return false;
    }
    if (!q.isEmpty())
    {
      String s = (String) ((Object[]) q.poll())[0];
      m_lastChunk += s;
      if (m_lastChunk.contains(m_separator))
      {
        boolean dangling = !m_lastChunk.endsWith(m_separator);
        String[] parts = s.split(m_separator);
        for (int i = 0; i < parts.length - (dangling ? 1 : 0); i++)
        {
          prepareChunk(parts[i], outputs);
        }
        if (dangling)
        {
          m_lastChunk = parts[parts.length - 1];
        }
        else
        {
          m_lastChunk = "";
        }
      }
    }
    return b;
  }
  
  protected void prepareChunk(String line, Queue<Object[]> outputs)
  {
    if (m_trim)
    {
      line = line.trim();
    }
    if (m_addCrlf)
    {
      line += CRLF;
    }
    outputs.add(new Object[] { line });
  }

}
