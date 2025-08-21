/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2019 Sylvain Hallé

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
package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.clone.ClonePrinter;
import ca.uqac.lif.azrael.clone.CloneReader;
import ca.uqac.lif.cep.tmf.BlackHole;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import java.util.Queue;
import org.junit.Test;

/**
 * Unit tests for the {@link Adder} class.
 * @author Sylvain Hallé
 */
public class AdderTest
{
  @Test
  public void test1()
  {
    QueueSource src1 = new QueueSource().setEvents(3, 1, 4, 1);
    QueueSource src2 = new QueueSource().setEvents(2, 7, 1, 8);
    Adder add = new Adder();
    Connector.connect(src1, 0, add, 0);
    Connector.connect(src2, 0, add, 1);
    Pullable p = add.getPullableOutput();
    assertEquals(5, ((Integer) p.pull()).intValue());
    assertEquals(8, ((Integer) p.pull()).intValue());
    assertEquals(5, ((Integer) p.pull()).intValue());
    assertEquals(9, ((Integer) p.pull()).intValue());
  }
  
  @Test
  public void testSerialization1() throws ProcessorException, PrintException, ReadException
  {
    ClonePrinter printer = new ClonePrinter();
    CloneReader reader = new CloneReader();
    Adder proc = new Adder();
    BlackHole bh = new BlackHole();
    Connector.connect(proc, bh);
    proc.getPushableInput(0).push(8);
    Object e = printer.print(proc);
    assertNotNull(e);
    Object o = reader.read(e);
    assertNotNull(o);
    assertTrue(o instanceof Adder);
    Adder proc2 = (Adder) o;
    assertFalse(proc == proc2);
    assertEquals(0, proc2.getInputCount());
    assertEquals(0, proc2.getOutputCount());
    QueueSink sink = new QueueSink();
    Queue<Object> q = sink.getQueue();
    Connector.connect(proc2, sink);
    Pushable p1 = proc2.getPushableInput(0);
    Pushable p2 = proc2.getPushableInput(1);
    p1.push(7);
    assertTrue(q.isEmpty());
    p2.push(3);
    assertFalse(q.isEmpty());
    assertEquals(11, q.remove());
  }
}