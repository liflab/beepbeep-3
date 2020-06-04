/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2020 Sylvain Hallé

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
package ca.uqac.lif.cep.tmf;

import org.junit.Test;

import static org.junit.Assert.*;

import java.util.NoSuchElementException;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SynchronousProcessor;

/**
 * Unit tests for the {@link Multiplex} processor.
 * @author Sylvain Hallé
 */
public class MultiplexTest
{
  @Test
  public void testPull1()
  {
    ImpoliteQueueSource qs1 = new ImpoliteQueueSource();
    qs1.setEvents(1, 2, 3).loop(false);
    ImpoliteQueueSource qs2 = new ImpoliteQueueSource();
    qs2.setEvents(4, 5).loop(false);
    Multiplex m = new Multiplex(2);
    Connector.connect(qs1, 0, m, 0);
    Connector.connect(qs2, 0, m, 1);
    Pullable p = m.getPullableOutput();
    assertTrue(p.hasNext());
    int x = (Integer) p.pull();
    assertEquals(1, x);
    x = (Integer) p.pull();
    assertEquals(4, x);
    x = (Integer) p.pull();
    assertEquals(2, x);
    x = (Integer) p.pull();
    assertEquals(5, x);
    x = (Integer) p.pull();
    assertEquals(3, x);
    assertFalse(p.hasNext());
  }
  
  @Test
  public void testPull2()
  {
    ImpoliteQueueSource qs1 = new ImpoliteQueueSource();
    qs1.setEvents(1, 2, 3).loop(false);
    ImpoliteQueueSource qs2 = new ImpoliteQueueSource();
    qs2.setEvents(4, 5).loop(false);
    Multiplex m = new Multiplex(2);
    Connector.connect(qs2, 0, m, 0);
    Connector.connect(qs1, 0, m, 1);
    Pullable p = m.getPullableOutput();
    assertTrue(p.hasNext());
    int x = (Integer) p.pull();
    assertEquals(4, x);
    x = (Integer) p.pull();
    assertEquals(1, x);
    x = (Integer) p.pull();
    assertEquals(5, x);
    x = (Integer) p.pull();
    assertEquals(2, x);
    x = (Integer) p.pull();
    assertEquals(3, x);
    assertFalse(p.hasNext());
  }
  
  /**
   * A QueueSource that throws an exception when being pulled and
   * no more event is available.
   */
  protected static class ImpoliteQueueSource extends QueueSource
  {
    @Override
    public ImpoliteQueueSource setEvents(Object ... objects)
    {
      super.setEvents(objects);
      return this;
    }
    
    @Override
    public synchronized Pullable getPullableOutput(int index)
    {
      if (m_outputPullables[index] == null)
      {
        m_outputPullables[index] = new ImpoliteOutputPullable(index);
      }
      return m_outputPullables[index];
    }
    
    public class ImpoliteOutputPullable extends SynchronousProcessor.OutputPullable
    {
      public ImpoliteOutputPullable(int index)
      {
        super(index);
      }
      
      @Override
      public synchronized Object pull()
      {
        Object o = super.pull();
        if (o == null)
        {
          throw new NoSuchElementException();
        }
        return o;
      }
    }
  }
}
