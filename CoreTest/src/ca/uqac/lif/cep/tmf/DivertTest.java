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
package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.*;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import java.util.Queue;
import org.junit.Test;

/**
 * Unit tests for the {@link Divert} processor.
 */
public class DivertTest
{
  @Test
  public void testDuplicate1()
  {
    Divert div = new Divert();
    Divert div_dup = div.duplicate(false);
    assertNotNull(div_dup);
    assertNotEquals(div, div_dup);
  }
  
  @Test
  public void testDuplicate2()
  {
    Divert div = new Divert();
    Divert div_dup = div.duplicate(true);
    assertNotNull(div_dup);
    assertNotEquals(div, div_dup);
  }
  
  @Test(expected=IndexOutOfBoundsException.class)
  public void testGetPullable()
  {
    Divert div = new Divert();
    div.getPullableOutput(1);
  }
  
  @Test(expected=IndexOutOfBoundsException.class)
  public void testGetPushable()
  {
    Divert div = new Divert();
    div.getPushableInput(1);
  }
  
  @Test
  public void testPush1()
  {
    Divert div = new Divert();
    QueueSink qs1 = new QueueSink();
    QueueSink qs2 = new QueueSink();
    Queue<Object> q1 = qs1.getQueue();
    Queue<Object> q2 = qs2.getQueue();
    Connector.connect(div, qs1);
    Connector.connect(div, qs2);
    Pushable p = div.getPushableInput();
    p.push("foo");
    assertEquals("foo", (String) q1.remove());
    assertTrue(q2.isEmpty());
    div.divertTo(1);
    p.push("bar");
    assertEquals("bar", (String) q2.remove());
    p.push("baz");
    assertTrue(q1.isEmpty());
    assertEquals(div, p.getProcessor());
    assertEquals(0, p.getPosition());
    
  }
  
  @Test(expected=IndexOutOfBoundsException.class)
  public void testPush2()
  {
    Divert div = new Divert();
    QueueSink qs1 = new QueueSink();
    QueueSink qs2 = new QueueSink();
    Connector.connect(div, qs1);
    Connector.connect(div, qs2);
    div.divertTo(2); // out of bounds
    Pushable p = div.getPushableInput();
    p.push("foo");
  }
  
  @Test
  public void testPull1()
  {
    QueueSource src = new QueueSource();
    src.setEvents(0, 1, 2, 3, 4);
    Divert div = new Divert();
    Connector.connect(src, div);
    Pullable p = div.getPullableOutput(0);
    Object o;
    o = p.pull();
    assertEquals(0, o);
    assertTrue(p.hasNext());
    o = p.pull();
    assertEquals(1, o);
    o = p.pullSoft();
    assertEquals(2, o);
    o = p.next();
    assertEquals(3, o);
    assertEquals(div, p.getProcessor());
    assertEquals(0, p.getPosition());
    assertEquals(p, p.iterator());
    // These three calls should have no effect and cause no error
    p.start();
    p.stop();
    p.dispose();
  }
  
  @Test
  public void testPull2()
  {
    QueueSource src = new QueueSource();
    src.setEvents(0, 1, 2, 3, 4);
    Divert div = new Divert();
    Connector.connect(src, div);
    Passthrough pt1 = new Passthrough();
    Passthrough pt2 = new Passthrough();
    Connector.connect(div, pt1);
    Connector.connect(div, pt2);
    Pullable p1 = pt1.getPullableOutput();
    Pullable p2 = pt2.getPullableOutput();
    Object o;
    o = p1.pull();
    assertEquals(0, o);
    o = p2.pull();
    assertEquals(1, o);
    o = p1.pull();
    assertEquals(2, o);
  }
}
