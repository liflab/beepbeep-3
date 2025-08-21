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
 * Extracts character strings from a Java {@link InputStream}.
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class ReadStringStream extends ReadInputStream
{
  /**
   * Creates a new stream reader
   * 
   * @param is
   *          The input stream to read from
   */
  public ReadStringStream(/*@ non_null @*/ InputStream is)
  {
    super(is);
  }
  
  /**
  * Creates a new stream reader
  * 
  * @param f The file to read from
  * @throws FileNotFoundException Thrown if the file does not exist
  */
 public ReadStringStream(/*@ non_null @*/ File f) throws FileNotFoundException
 {
   super(f);
 }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
  	Queue<Object[]> q = new ArrayDeque<Object[]>(1);
  	boolean b = super.compute(inputs, q);
  	if (!q.isEmpty())
  	{
  		Object[] arr = q.poll();
  		outputs.add(new Object[] {new String((char[]) arr[0])});
  	}
  	return b;
  }
}
