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
package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.ApplyFunction;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the basic {@link Processor} functionalities.
 */
public class ProcessorTest
{

	@Test
	public void testContext1()
	{
		Passthrough pt = new Passthrough();
		Context c = pt.newContext();
		assertTrue(c.isEmpty());
	}
	
	@Test
	public void testContext2()
	{
		Passthrough pt = new Passthrough();
		Context c = pt.getContext();
		assertTrue(c.isEmpty());
	}
	
	@Test
	public void testContext3()
	{
		Passthrough pt = new Passthrough();
		pt.setContext("a", 0);
		assertEquals(0, pt.getContext("a"));
	}
	
	@Test
	public void testContext4()
	{
		Passthrough pt = new Passthrough();
		Context c = pt.getContext();
		c.put("a", 0);
		assertEquals(0, pt.getContext("a"));
		c = pt.getContext();
		assertEquals(0, c.get("a"));
	}
	
	@Test
	public void testContext5()
	{
		Passthrough pt = new Passthrough();
		Context c = pt.newContext();
		c.put("a", 0);
		assertTrue(pt.getContext().isEmpty());
		pt.setContext(c);
		assertEquals(0, pt.getContext("a"));
		assertNull(pt.getContext("b"));
		pt.setContext("b", 1);
		assertEquals(1, pt.getContext("b"));
	}
	
	@Test
	public void testContext6()
	{
		Passthrough pt = new Passthrough();
		assertNull(pt.getContext("a"));
	}
	
	@Test
	public void testAllNull1()
	{
		Object[] os = new Object[3];
		assertTrue(Processor.allNull(os));
	}
	
	@Test
	public void testAllNull2()
	{
		Object[] os = new Object[]{null, 0, null};
		assertFalse(Processor.allNull(os));
	}
	
	@Test
	public void testDuplicate()
	{
		ApplyFunction pt1 = new ApplyFunction(Numbers.addition);
		pt1.setContext("a", 0);
		ApplyFunction pt2 = pt1.duplicate();
		assertNotEquals(pt1.getId(), pt2.getId());
		assertEquals(0, pt2.getContext("a"));
		pt1.setContext("a", 1);
		assertEquals(0, pt2.getContext("a"));
	}
	
	@Test
	public void testEquals()
	{
		ApplyFunction pt1 = new ApplyFunction(Numbers.addition);
		ApplyFunction pt2 = new ApplyFunction(Numbers.addition);
		assertTrue(pt1.equals(pt1));
		assertFalse(pt1.equals(pt2));
		assertFalse(pt1.equals(Numbers.addition));
		assertFalse(pt1.equals(null));
		
	}
	
	@Test
	public void testStartStop() throws ProcessorException
	{
		Processor.startAll();
		ConnectorTest.Oranges o1 = new ConnectorTest.Oranges();
		ConnectorTest.Oranges o2 = new ConnectorTest.Oranges();
		Processor.startAll(o1, null, o2);
		assertTrue(o1.started && o2.started);
		Processor.stopAll(o1, o2, null);
		assertTrue(!o1.started && !o2.started);
	}
	
	@Test
	public void testPush1() 
	{
		QueueSource cp = new QueueSource(1);
		cp.addEvent("A");
		QueueSink qs = new QueueSink(1);
		Connector.connect(cp, qs);
		cp.push();
		if (qs.getQueue(0).size() != 1)
		{
			fail("Expected one event in sink queue");
		}
		cp.push();
		if (qs.getQueue(0).size() != 2)
		{
			fail("Expected two events in sink queue");
		}
	}
	
	@Test
	public void testPull1() 
	{
		QueueSource cp = new QueueSource(1);
		cp.addEvent("A");
		String recv;
		Pullable p = cp.getPullableOutput(0);
		recv = (String) p.pullSoft();
		if (recv == null)
		{
			fail("Expected a string, got null");
		}
		if (recv.compareTo("A") != 0)
		{
			fail("Expected 'A', got " + recv);
		}
	}
	
	

	
	@Test
	public void testAdditionPush1() 
	{
		Vector<Object> l_input1 = new Vector<Object>();
		l_input1.add(1);
		l_input1.add(2);
		l_input1.add(3);
		Vector<Object> l_input2 = new Vector<Object>();
		l_input2.add(6);
		l_input2.add(4);
		l_input2.add(0);
		QueueSource input1 = new QueueSource(1);
		input1.setEvents(l_input1);
		QueueSource input2 = new QueueSource(1);
		input2.setEvents(l_input2);
		ApplyFunction add = new ApplyFunction(Numbers.addition);
		Connector.connect(input1, 0, add, 0);
		Connector.connect(input2, 0, add, 1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(add, sink);
		Number recv;
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // 1 + 6
		if (recv == null || recv.intValue() != 7)
		{
			fail("Expected 7, got " + recv);
		}
		input1.push(); // We only push on first input
		recv = (Number) sink.remove()[0]; // 2 + ?
		if (recv != null)
		{
			// Can't compute an output event; we're waiting for right input
			fail("Expected null, got " + recv);
		}
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // 2 + 4
		if (recv == null || recv.intValue() != 6)
		{
			fail("Expected 10, got " + recv);
		}
		input2.push();
		// Only need to push on right; left already in queue
		recv = (Number) sink.remove()[0]; // 3 + 0
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3, got " + recv);
		}
	}

	@Test
	public void testBinaryPull() 
	{
		QueueSource src_left = new QueueSource();
		QueueSource src_right = new QueueSource();
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(new Integer(1));
			input_events.add(new Integer(2));
			src_left.setEvents(input_events);
		}
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(null);
			input_events.add(new Integer(10));
			input_events.add(new Integer(11));
			src_right.setEvents(input_events);
		}
		ApplyFunction add = new ApplyFunction(Numbers.addition);
		Connector.connect(src_left, 0, add, 0);
		Connector.connect(src_right, 0, add, 1);
		Pullable p = add.getPullableOutput(0);
		Number n;
		n = (Number) p.pullSoft();
		assertNull(n);
		n = (Number) p.pullSoft();
		assertEquals(11, n.intValue());
	}
	
	/**
	 * This test does not assert anything. It is used for step-by-step debugging
	 * of the {@link SingleProcessor.OutputPullable#hasNextSoft()} method.
	 */
	@Test
	public void testHasNext() 
	{
		Vector<Object> events = new Vector<Object>();
		events.add("A");
		events.add("B");
		events.add("C");
		events.add("D");
		QueueSource cp = new QueueSource(1);
		cp.setEvents(events);
		Passthrough pt = new Passthrough(1);
		Connector.connect(cp, pt);
		Pullable p = pt.getPullableOutput(0);
		for (int i = 0; i < 10; i++)
		{
			if (p.hasNextSoft() == NextStatus.YES)
			{
				p.pullSoft();
			}
		}
		assertTrue(true);
	}

	@Test
	@SuppressWarnings("unused")
	public void testProcessorException2()
	{
		// Constructor test; we just check that it runs
		ProcessorException pe = new ProcessorException("foo");
	}
	
	@Test
	@SuppressWarnings("unused")
	public void testProcessorException3()
	{
		// Constructor test; we just check that it runs
		try
		{
			// Create an exception
			int a = 0;
			int b = 4 / a;
		}
		catch (Exception e)
		{
			ProcessorException pe = new ProcessorException(e);
		}
	}
	
	public static class Sum extends Cumulate
	{
		@SuppressWarnings({ "rawtypes", "unchecked" })
		public Sum()
		{
			super(new CumulativeFunction(Numbers.addition));
		}
	}	
}
