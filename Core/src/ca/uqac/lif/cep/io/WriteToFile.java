/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2018 Sylvain Hallé

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

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.tmf.Sink;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Queue;

/**
 * Writes input events to one or more files.
 * @author Sylvain Hallé
 */
public class WriteToFile extends Sink
{
  /**
   * A counter keeping track of the number of files output so far
   */
  protected int m_outputCount;

  /**
   * The pattern used to create names for each successive file
   */
  protected String m_filenamePattern;

  /**
   * Creates a new file writer
   * @param pattern The pattern used to create filenames
   */
  public WriteToFile(/*@ non_null @*/ String pattern)
  {
    super(1);
    m_filenamePattern = pattern;
    m_outputCount = 0;
  }

  @Override
  public void reset()
  {
    super.reset();
    m_outputCount = 0;
  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    String new_filename = createFilename();
    m_outputCount++;
    try
    {
      FileOutputStream fos = new FileOutputStream(new File(new_filename));
      BufferedOutputStream bos = new BufferedOutputStream(fos);
      if (inputs[0] instanceof byte[])
      {
        bos.write((byte[]) inputs[0]);
      }
      bos.close();
    }
    catch (FileNotFoundException e)
    {
      throw new ProcessorException(e);
    }
    catch (IOException e)
    {
      throw new ProcessorException(e);
    }
    return true;
  }

  @Override
  public Processor duplicate(boolean with_state)
  {
    throw new UnsupportedOperationException();
  }

  /**
   * Generates the name of the next file to write to. This name is computed
   * by replacing special characters in a predefined pattern with the
   * current values held by the processor.
   * @return The new filename
   */
  /*@ pure non_null @*/ protected String createFilename()
  {
    String new_filename = m_filenamePattern;
    new_filename = new_filename.replaceAll("%n", Integer.toString(m_outputCount));
    return new_filename;
  }
}
