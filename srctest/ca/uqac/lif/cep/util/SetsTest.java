/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2024 Sylvain Hallé

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

import static org.junit.Assert.*;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.functions.FunctionsTest;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import org.junit.Test;

/**
 * Unit tests for the {@link ca.uqac.lif.cep.util.Sets Sets} utility class.
 */
public class SetsTest
{
  @Test
  @SuppressWarnings("unchecked")
  public void testSetsPut1()
  {
    Set<Object> m1, m2;
    QueueSource s1 = new QueueSource().setEvents(0, 1, 2);
    Sets.PutInto pi = new Sets.PutInto();
    assertEquals(Set.class, pi.getOutputType(0));
    Connector.connect(s1, pi);
    Pullable p = pi.getPullableOutput();
    m1 = (Set<Object>) p.pull();
    assertEquals(1, m1.size());
    m2 = (Set<Object>) p.pull();
    assertTrue(m1 == m2);
    assertEquals(2, m1.size());
    pi.reset();
    // A new set has been created, so m1 is unchanged
    assertEquals(2, m1.size());
  }
  
  @Test
  @SuppressWarnings("unchecked")
  public void testSetsPut2()
  {
    Set<Object> m1, m2;
    QueueSource s1 = new QueueSource().setEvents(0, 1, 2);
    Sets.PutIntoNew pi = new Sets.PutIntoNew();
    assertEquals(Set.class, pi.getOutputType(0));
    Connector.connect(s1, 0, pi, 0);
    Pullable p = pi.getPullableOutput();
    m1 = (Set<Object>) p.pull();
    assertEquals(1, m1.size());
    m2 = (Set<Object>) p.pull();
    assertFalse(m1 == m2);
    assertEquals(2, m2.size());
    pi.reset();
    assertEquals(1, m1.size());
  }
  
  @Test
  public void testSubset()
  {
    Set<Integer> s1 = new HashSet<Integer>();
    s1.add(0);
    s1.add(1);
    Set<Integer> s2 = new HashSet<Integer>();
    s2.add(0);
    s2.add(1);
    s2.add(2);
    assertTrue((Boolean) FunctionsTest.evaluate(Sets.isSubsetOrEqual, s1, s2));
    s1.add(3);
    assertFalse((Boolean) FunctionsTest.evaluate(Sets.isSubsetOrEqual, s1, s2));
  }
  
  @Test
  public void testReset1()
  {
    Sets.PutInto pi = new Sets.PutInto();
    QueueSink qs = new QueueSink();
    Connector.connect(pi, qs);
    Pushable p = pi.getPushableInput();
    Queue<Object> q = qs.getQueue();
    p.push("foo");
    Set<?> set1 = (Set<?>) q.remove();
    assertEquals(1, set1.size());
    assertTrue(set1.contains("foo"));
    pi.reset();
    p.push("bar");
    Set<?> set2 = (Set<?>) q.remove();
    assertFalse(set1 == set2); // A new set has been created
    assertEquals(1, set2.size());
    assertFalse(set1.contains("bar"));
    assertTrue(set2.contains("bar"));
    assertTrue(set1.contains("foo")); // set1 is unchanged
  }
  
  @Test
  public void testIntersect1()
  {
  	Set<?> set1;
  	Sets.Intersect inter = new Sets.Intersect();
  	QueueSink qs = new QueueSink();
    Connector.connect(inter, qs);
    Pushable p = inter.getPushableInput();
    Queue<Object> q = qs.getQueue();
    p.push(Arrays.asList("foo", "bar", "baz"));
    set1 = (Set<?>) q.remove();
    assertEquals(3, set1.size());
    p.push(Arrays.asList("foo", "bar", "baz", "biz"));
    set1 = (Set<?>) q.remove();
    assertEquals(3, set1.size());
    p.push(Arrays.asList("foo", "baz"));
    set1 = (Set<?>) q.remove();
    assertEquals(2, set1.size());
    p.push(Arrays.asList("foo", "buzz"));
    set1 = (Set<?>) q.remove();
    assertEquals(1, set1.size());
  }
}
