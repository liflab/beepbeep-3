package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.clone.ClonePrinter;
import ca.uqac.lif.azrael.clone.CloneReader;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Utilities;
import java.util.Queue;
import org.junit.Test;

/**
 * Unit tests for the {@link Trim} processor.
 */
public class TrimTest
{
  @Test
  public void testTrim() 
  {
    Trim d = new Trim(3);
    QueueSink qs = new QueueSink(1);
    Connector.connect(d, qs);
    Pushable in = d.getPushableInput(0);
    Queue<Object> queue = qs.getQueue(0);
    for (int k = 0; k < 2; k++)
    {
      in.push(0);
      assertTrue(queue.isEmpty());
      in.push(1);
      assertTrue(queue.isEmpty());
      in.push(2);
      assertTrue(queue.isEmpty());
      in.push(3);
      Utilities.queueContains(3, queue);
      in.push(4);
      Utilities.queueContains(4, queue);
      d.reset();
    }
  }
  
  @Test
  public void testSerialization1() throws ProcessorException, PrintException, ReadException
  {
    ClonePrinter printer = new ClonePrinter();
    CloneReader reader = new CloneReader();
    Trim proc = new Trim(1);
    Object e = printer.print(proc);
    assertNotNull(e);
    Object o = reader.read(e);
    assertNotNull(o);
    assertTrue(o instanceof Trim);
    Trim proc2 = (Trim) o;
    assertFalse(proc == proc2);
    assertEquals(1, proc2.getDelay());
    assertEquals(0, proc2.getInputCount());
    assertEquals(0, proc2.getOutputCount());
  }
  
  @Test
  public void testSerialization2() throws ProcessorException, PrintException, ReadException
  {
    ClonePrinter printer = new ClonePrinter();
    CloneReader reader = new CloneReader();
    Trim proc1 = new Trim(2);
    QueueSink sink1 = new QueueSink();
    Connector.connect(proc1, sink1);
    Pushable p1 = proc1.getPushableInput();
    p1.push("foo");
    Object e = printer.print(proc1);
    assertNotNull(e);
    Object o = reader.read(e);
    assertNotNull(o);
    assertTrue(o instanceof Trim);
    Trim proc2 = (Trim) o;
    assertFalse(proc1 == proc2);
    assertEquals(1, proc2.getInputCount());
    assertEquals(0, proc2.getOutputCount());
    QueueSink sink2 = new QueueSink();
    Connector.connect(proc2, sink2);
    Pushable p2 = proc2.getPushableInput();
    Queue<Object> q2 = sink2.getQueue();
    p2.push("bar");
    assertTrue(q2.isEmpty());
    p2.push("baz");
    assertFalse(q2.isEmpty());
  }
}
