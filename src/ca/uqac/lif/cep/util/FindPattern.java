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
package ca.uqac.lif.cep.util;

import ca.uqac.lif.cep.SynchronousProcessor;
import java.util.Queue;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Extracts chunks of an input stream based on a regular expression.
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class FindPattern extends SynchronousProcessor
{
  /**
   * The buffered contents of the string received so far
   */
  protected String m_contents;

  /**
   * The pattern to extract from the input stream
   */
  protected Pattern m_pattern;

  /**
   * Trims the pattern from leading and trailing spaces
   */
  protected boolean m_trim = true;

  /**
   * Creates a new pattern scanner
   * 
   * @param regex
   *          The regular expression defining the pattern to extract
   */
  public FindPattern(String regex)
  {
    this(Pattern.compile(regex));
  }

  /**
   * Creates a new pattern scanner
   * 
   * @param pattern
   *          The pattern to extract
   */
  public FindPattern(Pattern pattern)
  {
    super(1, 1);
    m_contents = "";
    m_pattern = pattern;
  }

  @Override
  public FindPattern duplicate(boolean with_state)
  {
    FindPattern fp = new FindPattern(m_pattern);
    fp.m_trim = m_trim;
    if (with_state)
    {
      fp.m_contents = new String(m_contents);
    }
    return fp;
  }

  /**
   * Sets whether to apply {@code trim()} to each output event
   * 
   * @param b
   *          Set to {@code true} to trim (default), {@code false} otherwise
   * @return This scanner
   */
  public FindPattern trim(boolean b)
  {
    m_trim = b;
    return this;
  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    m_contents += (String) inputs[0];
    Matcher mat = m_pattern.matcher(m_contents);
    int last_end = 0;
    while (mat.find())
    {
      String matched;
      if (mat.groupCount() > 0)
      {
        matched = mat.group(1);
        if (matched == null)
        {
          throw new Error("Capturing group 1 of " + m_pattern + "did not match in " + m_contents);
        }
      } else {
        matched = mat.group();
      }
      if (m_trim)
      {
        matched = matched.trim();
      }
      outputs.add(new Object[] { matched });
      last_end = mat.end();
    }
    m_contents = m_contents.substring(last_end);
    return true;
  }
}
