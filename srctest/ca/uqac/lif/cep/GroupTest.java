/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2022 Sylvain Hallé

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

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.Vector;

import org.junit.Test;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.clone.ClonePrinter;
import ca.uqac.lif.azrael.clone.CloneReader;
import ca.uqac.lif.cep.functions.ApplyFunction;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.cep.tmf.Fork;
import ca.uqac.lif.cep.tmf.BlackHole;
import ca.uqac.lif.cep.tmf.CountDecimate;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the {@link GroupProcessor}.
 * @author Sylvain Hallé
 */
public class GroupTest 
{
	@Test
	public void testGroup1() 
	{
		Passthrough pt1 = new Passthrough(1);
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.addProcessor(pt1);
		gp.associateInput(0, pt1, 0);
		gp.associateOutput(0, pt1, 0);
		Pushable push1 = gp.getPushableInput(0);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(gp, qsink);
		Queue<Object> queue = qsink.getQueue(0);
		push1.push(0);
		Utilities.queueContains(0, queue);
		push1.push(1);
		Utilities.queueContains(1, queue);
		push1.push(2);
		Utilities.queueContains(2, queue);
	}
	
	@Test
	public void testGroup2() 
	{
		Passthrough pt1 = new Passthrough(2);
		GroupProcessor gp = new GroupProcessor(2, 2);
		gp.addProcessor(pt1);
		gp.associateInput(0, pt1, 1);
		gp.associateInput(1, pt1, 0);
		gp.associateOutput(0, pt1, 0);
		gp.associateOutput(1, pt1, 1);
		Pushable push1 = gp.getPushableInput(0);
		assertNotNull(push1);
		Pushable push2 = gp.getPushableInput(1);
		assertNotNull(push2);
		QueueSink qsink = new QueueSink(2);
		Connector.connect(gp, qsink);
		Queue<Object> queue1 = qsink.getQueue(0);
		Queue<Object> queue2 = qsink.getQueue(1);
		push1.push(0);
		assertTrue(queue1.isEmpty());
		assertTrue(queue2.isEmpty());
		push2.push(100);
		Utilities.queueContains(100, queue1);
		Utilities.queueContains(0, queue2);
		push1.push(1);
		push2.push(101);
		Utilities.queueContains(101, queue1);
		Utilities.queueContains(1, queue2);
		push2.push(102);
		assertTrue(queue1.isEmpty());
		assertTrue(queue2.isEmpty());
	}
	
	@Test
	public void testGroup3() 
	{
		Passthrough pt1 = new Passthrough(1);
		Passthrough pt2 = new Passthrough(1);
		Connector.connect(pt1, pt2);
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.addProcessor(pt1);
		gp.addProcessor(pt2);
		gp.associateInput(0, pt1, 0);
		gp.associateOutput(0, pt2, 0);
		Pushable push1 = gp.getPushableInput(0);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(gp, qsink);
		Queue<Object> queue = qsink.getQueue(0);
		push1.push(0);
		Utilities.queueContains(0, queue);
		push1.push(1);
		Utilities.queueContains(1, queue);
		push1.push(2);
		Utilities.queueContains(2, queue);
	}

	@Test
	public void testClone1() 
	{
		Passthrough pt1 = new Passthrough(1);
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.addProcessor(pt1);
		gp.associateInput(0, pt1, 0);
		gp.associateOutput(0, pt1, 0);
		GroupProcessor gp_clone = (GroupProcessor) gp.duplicate();
		assertNotNull(gp_clone);
		// Make sure we don't refer accidentally to the original objects
		pt1 = null;
		gp = null;
		Pushable push1 = gp_clone.getPushableInput(0);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(gp_clone, qsink);
		Queue<Object> queue = qsink.getQueue(0);
		push1.push(0);
		Utilities.queueContains(0, queue);
		push1.push(1);
		Utilities.queueContains(1, queue);
		push1.push(2);
		Utilities.queueContains(2, queue);
	}
	
	@Test
	public void testClone2() 
	{
		Passthrough pt1 = new Passthrough(2);
		GroupProcessor gp = new GroupProcessor(2, 2);
		gp.addProcessor(pt1);
		gp.associateInput(0, pt1, 1);
		gp.associateInput(1, pt1, 0);
		gp.associateOutput(0, pt1, 0);
		gp.associateOutput(1, pt1, 1);
		GroupProcessor gp_clone = (GroupProcessor) gp.duplicate();
		// Make sure we don't refer accidentally to the original objects
		pt1 = null;
		gp = null;
		Pushable push1 = gp_clone.getPushableInput(0);
		assertNotNull(push1);
		Pushable push2 = gp_clone.getPushableInput(1);
		assertNotNull(push2);
		QueueSink qsink = new QueueSink(2);
		Connector.connect(gp_clone, qsink);
		Queue<Object> queue1 = qsink.getQueue(0);
		Queue<Object> queue2 = qsink.getQueue(1);
		push1.push(0);
		assertTrue(queue1.isEmpty());
		assertTrue(queue2.isEmpty());
		push2.push(100);
		Utilities.queueContains(100, queue1);
		Utilities.queueContains(0, queue2);
		push1.push(1);
		push2.push(101);
		Utilities.queueContains(101, queue1);
		Utilities.queueContains(1, queue2);
		push2.push(102);
		assertTrue(queue1.isEmpty());
		assertTrue(queue2.isEmpty());
	}
	
	@Test
	public void testClone3() 
	{
		Passthrough pt1 = new Passthrough(1);
		Passthrough pt2 = new Passthrough(1);
		Connector.connect(pt1, pt2);
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.addProcessor(pt1);
		gp.addProcessor(pt2);
		gp.associateInput(0, pt1, 0);
		gp.associateOutput(0, pt2, 0);
		GroupProcessor gp_clone = (GroupProcessor) gp.duplicate();
		assertNotNull(gp_clone);
		// Make sure we don't refer accidentally to the original objects
		pt1 = null;
		pt2 = null;
		gp = null;
		Pushable push1 = gp_clone.getPushableInput(0);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(gp_clone, qsink);
		Queue<Object> queue = qsink.getQueue(0);
		push1.push(0);
		Utilities.queueContains(0, queue);
		push1.push(1);
		Utilities.queueContains(1, queue);
		push1.push(2);
		Utilities.queueContains(2, queue);
	}
	
	@Test
	public void testClone4() 
	{
		Passthrough pt1 = new Passthrough(2);
		Passthrough pt2 = new Passthrough(2);
		Connector.connect(pt1, 0, pt2, 1);
		Connector.connect(pt1, 1, pt2, 0);
		GroupProcessor gp = new GroupProcessor(2, 2);
		gp.addProcessor(pt1);
		gp.addProcessor(pt2);
		gp.associateInput(0, pt1, 0);
		gp.associateInput(1, pt1, 1);
		gp.associateOutput(0, pt2, 0);
		gp.associateOutput(1, pt2, 1);
		GroupProcessor gp_clone = (GroupProcessor) gp.duplicate();
		pt1 = null;
		pt2 = null;
		gp = null;
		assertNotNull(gp_clone);
		Pushable push1 = gp_clone.getPushableInput(0);
		assertNotNull(push1);
		Pushable push2 = gp_clone.getPushableInput(1);
		assertNotNull(push2);
		QueueSink qsink = new QueueSink(2);
		Connector.connect(gp_clone, qsink);
		Queue<Object> queue1 = qsink.getQueue(0);
		Queue<Object> queue2 = qsink.getQueue(1);
		push1.push(0);
		assertTrue(queue1.isEmpty());
		assertTrue(queue2.isEmpty());
		push2.push(100);
		Utilities.queueContains(100, queue1);
		Utilities.queueContains(0, queue2);
		push1.push(1);
		push2.push(101);
		Utilities.queueContains(101, queue1);
		Utilities.queueContains(1, queue2);
		push2.push(102);
		assertTrue(queue1.isEmpty());
		assertTrue(queue2.isEmpty());
	}
	
	/**
	 * Try to clone a group processor that is already connected
	 * to something else. The goal of this test is only to check
	 * that the call to {@code duplicate()} does not throw an exception.
	 * @
	 */
	@Test
	public void testClone5() 
	{
		Passthrough pt1 = new Passthrough(2);
		Passthrough pt2 = new Passthrough(2);
		Connector.connect(pt1, 0, pt2, 1);
		Connector.connect(pt1, 1, pt2, 0);
		GroupProcessor gp = new GroupProcessor(2, 2);
		gp.addProcessor(pt1);
		gp.addProcessor(pt2);
		gp.associateInput(0, pt1, 0);
		gp.associateInput(1, pt1, 1);
		gp.associateOutput(0, pt2, 0);
		gp.associateOutput(1, pt2, 1);
		QueueSource qs = new QueueSource(2);
		qs.addEvent(0);
		Connector.connect(qs, gp);
		GroupProcessor gp_clone = (GroupProcessor) gp.duplicate();
		QueueSource qs2 = new QueueSource(2);
		qs2.addEvent(100);
		Connector.connect(qs2, gp_clone);
	}
	
	/**
	 * Clone a group within a group
	 */
	@Test
	public void testClone6() 
	{
		Object o = null;
		GroupIn g_within = new GroupIn(1, 1);
		{
			PassthroughIn pt = new PassthroughIn(1);
			g_within.addProcessor(pt);
			g_within.associateInput(0, pt, 0);
			g_within.associateOutput(0, pt, 0);
		}
		GroupProcessor g_out = new GroupProcessor(1, 1);
		g_out.addProcessor(g_within);
		Passthrough pt = new Passthrough(1);
		g_out.addProcessor(pt);
		Connector.connect(pt, g_within);
		g_out.associateInput(0, pt, 0);
		g_out.associateOutput(0, g_within, 0);
		// Check that this piping works
		{
			QueueSource qs = new QueueSource(1);
			qs.addEvent(0);
			Connector.connect(qs, g_out);
			Pullable pull1 = g_out.getPullableOutput(0);
			o = pull1.pull();
			assertNotNull(o);
			assertEquals(0, ((Number) o).intValue());
		}
		// Now clone
		GroupProcessor g_clone = (GroupProcessor) g_out.duplicate();
		{
			QueueSource qs = new QueueSource(1);
			qs.addEvent(0);
			Connector.connect(qs, g_clone);
			Pullable pull1 = g_clone.getPullableOutput(0);
			o = pull1.pull();
			assertNotNull(o);
			assertEquals(0, ((Number) o).intValue());
		}
	}
	
	/**
	 * Clone a group within a group.
	 * The difference with {@link #testClone6()} is that the
	 * group and the passthrough are in the reverse order.
	 */
	@Test
	public void testClone7() 
	{
		Object o = null;
		GroupIn g_within = new GroupIn(1, 1);
		{
			PassthroughIn pt = new PassthroughIn(1);
			g_within.addProcessor(pt);
			g_within.associateInput(0, pt, 0);
			g_within.associateOutput(0, pt, 0);
		}
		GroupProcessor g_out = new GroupProcessor(1, 1);
		g_out.addProcessor(g_within);
		Passthrough pt = new Passthrough(1);
		g_out.addProcessor(pt);
		Connector.connect(g_within, pt);
		g_out.associateInput(0, g_within, 0);
		g_out.associateOutput(0, pt, 0);
		// Check that this piping works
		{
			QueueSource qs = new QueueSource(1);
			qs.addEvent(0);
			Connector.connect(qs, g_out);
			Pullable pull1 = g_out.getPullableOutput(0);
			o = pull1.pull();
			assertNotNull(o);
			assertEquals(0, ((Number) o).intValue());
		}
		// Now clone
		GroupProcessor g_clone = (GroupProcessor) g_out.duplicate();
		{
			QueueSource qs = new QueueSource(1);
			qs.addEvent(0);
			Connector.connect(qs, g_clone);
			Pullable pull1 = g_clone.getPullableOutput(0);
			o = pull1.pull();
			assertNotNull(o);
			assertEquals(0, ((Number) o).intValue());
		}
	}
	
	@Test
	public void testGroupPull1() 
	{
		// Create the group
		ApplyFunction add = new ApplyFunction(Numbers.addition);
		GroupProcessor add_plus_10 = new GroupProcessor(2, 1);
		add_plus_10.addProcessor(add);
		add_plus_10.associateInput(0, add, 0);
		add_plus_10.associateInput(1, add, 1);
		add_plus_10.associateOutput(0, add, 0);
		
		// Connect the group to two sources and one sink
		Vector<Object> l_input1 = new Vector<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(6);
		QueueSource input1 = new QueueSource(1);
		input1.setEvents(l_input1);
		Vector<Object> l_input2 = new Vector<Object>();
		l_input2.add(1);
		l_input2.add(2);
		l_input2.add(3);
		l_input2.add(4);
		QueueSource input2 = new QueueSource(1);
		input2.setEvents(l_input2);
		Connector.connect(input1, 0, add_plus_10, 0);
		Connector.connect(input2, 0, add_plus_10, 1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(add_plus_10, sink);
		Number recv, expected;
		
		// Run
		sink.pull();
		expected = 3;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		sink.pull();
		expected = 5;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		sink.pull();
		expected = 7;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		sink.pull();
		expected = 10;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
	}
	
	@Test
	public void testGroupPush2() 
	{
		// Create the group
		ApplyFunction add = new ApplyFunction(Numbers.addition);
		Incrementer inc = new Incrementer(10);
		Connector.connect(inc, add);
		GroupProcessor add_plus_10 = new GroupProcessor(2, 1);
		add_plus_10.addProcessor(add);
		add_plus_10.associateInput(0, inc, 0);
		add_plus_10.associateInput(1, add, 1);
		add_plus_10.associateOutput(0, add, 0);
		
		// Connect the group to two sources and one sink
		Vector<Object> l_input1 = new Vector<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(6);
		QueueSource input1 = new QueueSource(1);
		input1.setEvents(l_input1);
		Vector<Object> l_input2 = new Vector<Object>();
		l_input2.add(1);
		l_input2.add(2);
		l_input2.add(3);
		l_input2.add(4);
		QueueSource input2 = new QueueSource(1);
		input2.setEvents(l_input2);
		Connector.connect(input1, 0, add_plus_10, 0);
		Connector.connect(input2, 0, add_plus_10, 1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(add_plus_10, sink);
		Number recv;
		
		// Run
		input1.push();
		input2.push();
		recv = (Number) sink.getQueue(0).remove();
		assertEquals(13, recv.intValue());
		input1.push();
		input2.push();
		recv = (Number) sink.getQueue(0).remove();
		assertEquals(15, recv.intValue());
		input1.push();
		input2.push();
		recv = (Number) sink.getQueue(0).remove();
		assertEquals(17, recv.intValue());
		input1.push();
		input2.push();
		recv = (Number) sink.getQueue(0).remove();
		assertEquals(20, recv.intValue());
	}
	
	@Test
	public void testGroupPush1() 
	{
		// Create the group
		ApplyFunction add = new ApplyFunction(Numbers.addition);
		GroupProcessor add_plus_10 = new GroupProcessor(2, 1);
		add_plus_10.addProcessor(add);
		add_plus_10.associateInput(0, add, 0);
		add_plus_10.associateInput(1, add, 1);
		add_plus_10.associateOutput(0, add, 0);
		
		// Connect the group to two sources and one sink
		Vector<Object> l_input1 = new Vector<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(6);
		QueueSource input1 = new QueueSource();
		input1.setEvents(l_input1);
		Vector<Object> l_input2 = new Vector<Object>();
		l_input2.add(1);
		l_input2.add(2);
		l_input2.add(3);
		l_input2.add(4);
		QueueSource input2 = new QueueSource(1);
		input2.setEvents(l_input2);
		Connector.connect(input1, 0, add_plus_10, 0);
		Connector.connect(input2, 0, add_plus_10, 1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(add_plus_10, sink);
		Number recv, expected;
		
		// Run
		input1.push();
		input2.push();
		expected = 3;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		input1.push();
		input2.push();
		expected = 5;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		input1.push();
		input2.push();
		expected = 7;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		input1.push();
		input2.push();
		expected = 10;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
	}
	
	@Test
	public void testReset() throws ProcessorException
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		ConnectorTest.Oranges v = new ConnectorTest.Oranges();
		gp.addProcessors(v);
		gp.associateInput(0, v, 0);
		gp.associateOutput(0, v, 0);
		gp.start();
		assertTrue(v.started);
		gp.stop();
		assertFalse(v.started);
		assertFalse(v.reset);
		gp.reset();
		assertTrue(v.reset);
	}
	
	@Test
	public void testContext() throws ProcessorException
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		ConnectorTest.Oranges v = new ConnectorTest.Oranges();
		gp.addProcessors(v);
		gp.associateInput(0, v, 0);
		gp.associateOutput(0, v, 0);
		gp.start();
		assertTrue(v.started);
		gp.stop();
		assertFalse(v.started);
		assertFalse(v.reset);
		gp.reset();
		assertTrue(v.reset);
		gp.setContext("a", 0);
		assertEquals(0, v.getContext().get("a"));
		assertEquals(0, gp.getContext().get("a"));
	}
	
	@Test
	public void testForkDuplicate() throws ProcessorException
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		Fork f = new Fork(2);
		gp.associateInput(0, f, 0);
		ApplyFunction af = new ApplyFunction(Numbers.addition);
		Connector.connect(f, 0, af, 0);
		Connector.connect(f, 1, af, 1);
		gp.associateOutput(0, af, 0);
		gp.addProcessors(f, af);
		GroupProcessor new_gp = (GroupProcessor) gp.duplicate();
		QueueSource src = new QueueSource().setEvents(1);
		Connector.connect(src, new_gp);
		Pullable p = new_gp.getPullableOutput();
		assertEquals(2f, p.pull());
	}
	
	public void testCrawlerBlackHole()
	{
		Passthrough pt = new Passthrough();
		BlackHole bh = new BlackHole();
		Connector.connect(pt, bh);
		CountCrawler cc = new CountCrawler();
		cc.crawl(bh);
		assertEquals(2, cc.m_visited.size());
	}
	
	@Test
	public void testCopyCrawlerBlackHole()
	{
		Passthrough pt = new Passthrough();
		BlackHole bh = new BlackHole();
		Connector.connect(pt, bh);
		CountCrawler cc = new CountCrawler();
		cc.crawl(bh);
		assertEquals(2, cc.m_visited.size());
	}
	
	@Test
	public void testPullable1() throws ProcessorException
	{
		QueueSource source = new QueueSource();
		source.setEvents(new Object[]{0, 1});
		GroupProcessor gp = new GroupProcessor(1, 1);
		Passthrough v = new Passthrough();
		gp.addProcessors(v);
		gp.associateInput(0, v, 0);
		gp.associateOutput(0, v, 0);
		Connector.connect(source, gp);
		Pullable p = gp.getPullableOutput();
		assertNotNull(p.pull());
		boolean got_exception = false;
		try
		{
			p.remove();
		}
		catch (UnsupportedOperationException e)
		{
			got_exception = true;
		}
		assertTrue(got_exception);
		assertEquals(gp.getId(), p.getProcessor().getId());
		assertEquals(0, p.getPosition());
	}
	
	@Test
  public void testSerialization1() throws ProcessorException, PrintException, ReadException
  {
	  ClonePrinter printer = new ClonePrinter();
    CloneReader reader = new CloneReader();
    GroupProcessor gp1 = new GroupProcessor(1, 1);
    Passthrough pt = new Passthrough();
    gp1.addProcessor(pt);
    gp1.associateInput(0, pt, 0);
    gp1.associateOutput(0, pt, 0);
    BlackHole bh = new BlackHole();
    Connector.connect(gp1, bh);
    Pushable p1 = gp1.getPushableInput();
    p1.push("foo");
    Object e = printer.print(gp1);
    assertNotNull(e);
    Object o = reader.read(e);
    assertNotNull(o);
    assertTrue(o instanceof GroupProcessor);
    GroupProcessor gp2 = (GroupProcessor) o;
    QueueSink sink = new QueueSink();
    Connector.connect(gp2, sink);
    Queue<Object> q = sink.getQueue();
    Pushable p2 = gp2.getPushableInput();
    p2.push("bar");
    assertFalse(q.isEmpty());
  }
  
  @Test
  public void testSerialization2() throws ProcessorException, PrintException, ReadException
  {
    ClonePrinter printer = new ClonePrinter();
    CloneReader reader = new CloneReader();
    GroupProcessor gp1 = new GroupProcessor(2, 1);
    Adder pt = new Adder();
    gp1.addProcessor(pt);
    gp1.associateInput(0, pt, 0);
    gp1.associateInput(1, pt, 1);
    gp1.associateOutput(0, pt, 0);
    BlackHole bh = new BlackHole();
    Connector.connect(gp1, bh);
    Pushable p1 = gp1.getPushableInput();
    p1.push(8);
    Object e = printer.print(gp1);
    assertNotNull(e);
    Object o = reader.read(e);
    assertNotNull(o);
    assertTrue(o instanceof GroupProcessor);
    GroupProcessor gp2 = (GroupProcessor) o;
    QueueSink sink = new QueueSink();
    Connector.connect(gp2, sink);
    Queue<Object> q = sink.getQueue();
    Pushable p2_1 = gp2.getPushableInput(0);
    Pushable p2_2 = gp2.getPushableInput(1);
    p2_1.push(7);
    assertTrue(q.isEmpty());
    p2_2.push(3);
    assertFalse(q.isEmpty());
    assertEquals(11, q.remove());
  }
  
  @Test
  public void testEndOfTrace1()
  {
    GroupProcessor g = new GroupProcessor(1, 2);
    Fork f = new Fork(2);
    g.associateInput(0, f, 0);
    Passthrough pt1 = new Passthrough();
    Passthrough pt2 = new Passthrough();
    Connector.connect(f, 0, pt1, 0);
    Connector.connect(f, 1, pt2, 0);
    g.associateOutput(0, pt1, 0);
    g.associateOutput(1, pt2, 0);
    QueueSink qs1 = new QueueSink();
    Connector.connect(g, 0, qs1, 0);
    QueueSink qs2 = new QueueSink();
    Connector.connect(g, 1, qs2, 0);
    g.addProcessors(f, pt1, pt2);
    Pushable p = g.getPushableInput(0);
    assertFalse(f.m_hasBeenNotifiedOfEndOfTrace[0]);
    assertFalse(pt1.m_hasBeenNotifiedOfEndOfTrace[0]);
    assertFalse(pt2.m_hasBeenNotifiedOfEndOfTrace[0]);
    assertFalse(qs1.m_hasBeenNotifiedOfEndOfTrace[0]);
    assertFalse(qs2.m_hasBeenNotifiedOfEndOfTrace[0]);
    p.notifyEndOfTrace();
    assertTrue(f.m_hasBeenNotifiedOfEndOfTrace[0]);
    assertTrue(pt1.m_hasBeenNotifiedOfEndOfTrace[0]);
    assertTrue(pt2.m_hasBeenNotifiedOfEndOfTrace[0]);
    assertTrue(qs1.m_hasBeenNotifiedOfEndOfTrace[0]);
    assertTrue(qs2.m_hasBeenNotifiedOfEndOfTrace[0]);
  }
  
  @Test
  public void testGetState1()
  {
  	GroupProcessor gp = new GroupProcessor(1, 1);
  	Passthrough pt = new Passthrough();
  	gp.addProcessor(pt);
  	gp.associateInput(0, pt, 0);
  	gp.associateOutput(0, pt, 0);
  	BlackHole h = new BlackHole();
  	Connector.connect(gp, h);
  	Pushable p = gp.getPushableInput();
  	Object s1 = gp.getState();
  	p.push(0);
  	Object s2 = gp.getState();
  	assertEquals(s1, s2);
  }
  
  @Test
  public void testGetState2()
  {
  	GroupProcessor gp = new GroupProcessor(1, 1);
  	Fork f = new Fork(2);
  	CountDecimate dec = new CountDecimate(2);
  	ApplyFunction add = new ApplyFunction(Numbers.addition);
  	Connector.connect(f, 0, dec, 0);
  	Connector.connect(dec, 0, add, 0);
  	Connector.connect(f, 1, add, 1);
  	gp.addProcessors(f, dec, add);
  	gp.associateInput(0, f, 0);
  	gp.associateOutput(0, add, 0);
  	BlackHole h = new BlackHole();
  	Connector.connect(gp, h);
  	Pushable p = gp.getPushableInput();
  	Object s1 = gp.getState();
  	p.push(0);
  	Object s2 = gp.getState();
  	assertNotEquals(s1, s2);
  }
  
  public static class ProcessorWrap extends SynchronousProcessor
  {
    protected Processor m_processor;
    
    protected Pushable[] m_pushables;
    
    protected QueueSink m_sink;
    
    public ProcessorWrap(Processor p)
    {
      super(p.getInputArity(), p.getOutputArity());
      m_processor = p;
      m_pushables = new Pushable[p.getInputArity()];
      for (int i = 0; i < m_pushables.length; i++)
      {
        Pushable pu = m_processor.getPushableInput(i);
        m_pushables[i] = pu;
      }
      m_sink = new QueueSink(p.getOutputArity());
      for (int i = 0; i < p.getOutputArity(); i++)
      {
        Connector.connect(m_processor, i, m_sink, i);
      }
    }

    @Override
    protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
    {
      for (int i = 0; i < inputs.length; i++)
      {
        m_pushables[i].push(inputs[i]);
      }
      while (!m_sink.getQueue().isEmpty())
      {
        Object[] front = new Object[m_sink.getOutputArity()];
        for (int i = 0; i < m_sink.getOutputArity(); i++)
        {
          front[i] = m_sink.getQueue(i).remove();
        }
        outputs.add(front);
      }
      return true;
    }
    
    @Override
    protected boolean onEndOfTrace(Queue<Object[]> queue)
    {
      return false;
    }
    
    public Pushable getPushableInput(int index)
    {
      if (m_inputPushables[index] == null)
      {
        m_inputPushables[index] = new InputPushable(index);
      }
      return m_inputPushables[index];
    }

    @Override
    public Processor duplicate(boolean with_state)
    {
      // TODO Auto-generated method stub
      return null;
    }
  }
	
	public static class Incrementer extends ApplyFunction
	{
		public Incrementer(int increment)
		{
			super(new IncrementFunction(increment));
		}
	}
	
	public static class IncrementFunction extends UnaryFunction<Number,Number>
	{
		int m_increment;
		
		public IncrementFunction(int increment)
		{
			super(Number.class, Number.class);
			m_increment = increment;
		}
		
		@Override
		public Number getValue(Number x)
		{
			return x.intValue() + m_increment;
		}	
	}

	public static class PassthroughIn extends Passthrough
	{

		public PassthroughIn(int arity) 
		{
			super(arity);
		}
		
		@Override
		public PassthroughIn duplicate(boolean with_state)
		{
			return new PassthroughIn(getInputArity());
		}
		
	}
	
	public static class GroupIn extends GroupProcessor
	{

		public GroupIn(int in_arity, int out_arity) {
			super(in_arity, out_arity);
			// TODO Auto-generated constructor stub
		}
		
		@Override
		public GroupIn duplicate(boolean with_state)
		{
			GroupIn in = new GroupIn(getInputArity(), getOutputArity());
			super.cloneInto(in, with_state);
			return in;
		}
	}
	
	public static class CountCrawler extends PipeCrawler
	{
		Set<Processor> m_visited = new HashSet<Processor>();
		
		@Override
		public void visit(Processor p)
		{
			m_visited.add(p);
			
		}
	}
}
