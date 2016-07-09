/*
    Cornipickle, validation of layout bugs in web applications
    Copyright (C) 2015 Sylvain HallÃ©

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

import java.io.ByteArrayInputStream;
import java.io.InputStream;

public class StringUtils
{
  /**
   * Wraps a string word-wise after a specified number of characters.
   * Found on <a href="http://stackoverflow.com/a/4212726">StackOverflow</a>.
   * @param s The string to wrap
   * @param num_chars The number of characters
   * @return The wrapped string
   */
  public static String wordWrap(String s, int num_chars)
  {
    StringBuilder sb = new StringBuilder(s);
    return wordWrap(sb, num_chars);
  }
  
  /**
   * Same as {@link #wordWrap(String, int)} for a StringBuilder
   * @param sb The string to wrap
   * @param num_chars The number of characters
   * @param newline_char The string representing what to put for a
   *   new line
   * @return The wrapped string
   */
  public static String wordWrap(StringBuilder sb, int num_chars, String newline_char)
  {
    int i = 0;
    while (i + num_chars < sb.length() && (i = sb.lastIndexOf(" ", i + num_chars)) != -1)
    {
        sb.replace(i, i + 1, newline_char);
    }
    return sb.toString();
  }
  
  /**
   * Same as {@link #wordWrap(String, int)} for a StringBuilder
   * @param sb The string builder to wrap
   * @param num_chars The number of characters
   * @return The wrapped string
   */
  public static String wordWrap(StringBuilder sb, int num_chars)
  {
    return wordWrap(sb, num_chars, "\n");
  }
  
  /**
   * Prepends a string to each line of another
   * @param p The string to prepend
   * @param b The (multi-line) input string
   * @return The prepended string
   */
  public static String prepend(String p, StringBuilder b)
  {
    return prepend(p, b.toString());
  }
  
  /**
   * Prepends a string to each line of another
   * @param p The string to prepend
   * @param b The (multi-line) input string
   * @return The prepended string
   */
  public static String prepend(String p, String b)
  {
    String[] lines = b.split("\n");
    StringBuilder out = new StringBuilder();
    for (String line : lines)
    {
      out.append(p).append(line).append("\n");
    }
    return out.toString();    
  }
  
  /**
   * Converts a string into an input stream
   * @param s The string to read from
   * @return The input stream with the contents of the string
   */
  public static InputStream toInputStream(String s)
  {
	  InputStream stream = new ByteArrayInputStream(s.getBytes());
	  return stream;
  }
  
}
