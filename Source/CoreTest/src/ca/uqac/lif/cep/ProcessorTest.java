/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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

import java.util.LinkedList;
import java.util.Queue;
import java.util.Vector;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.eml.numbers.Addition;
import ca.uqac.lif.cep.eml.numbers.CumulativeSum;
import ca.uqac.lif.cep.eml.numbers.Incrementer;
import ca.uqac.lif.cep.eml.numbers.IsEven;
import ca.uqac.lif.cep.epl.CountDecimate;
import ca.uqac.lif.cep.epl.Filter;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.epl.QueueSource;
import ca.uqac.lif.cep.epl.Window;

public class ProcessorTest
{

	@Before
	public void setUp() throws Exception
	{
		// Nothing to do
	}
	
	@Test
	public void testPush1()
	{
		QueueSource cp = new QueueSource("A", 1);
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
		QueueSource cp = new QueueSource("A", 1);
		String recv;
		Pullable p = cp.getPullableOutput(0);
		recv = (String) p.pull();
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
	public void testWindowPull1()
	{
		Number recv;
		QueueSource cs = new QueueSource(1, 1); // Sequence of 1s
		Window wp = new Window(new CumulativeSum(), 3);
		Connector.connect(cs, wp);
		Pullable p = wp.getPullableOutput(0);
		// We must pull three times to get the first output
		recv = (Number) p.pull();
		if (recv != null)
		{
			fail("Expected null on first pull, got " + recv);
		}
		recv = (Number) p.pull();
		if (recv != null)
		{
			fail("Expected null on second pull, got " + recv);
		}
		recv = (Number) p.pull();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on third pull, got " + recv);
		}
		recv = (Number) p.pull();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on fourth pull, got " + recv);
		}
	}
	
	@Test
	public void testWindowPull2()
	{
		Number recv;
		QueueSource cs = new QueueSource(1, 1); // Sequence of 1s
		Window wp = new Window(new CumulativeSum(), 3);
		Connector.connect(cs, wp);
		Pullable p = wp.getPullableOutput(0);
		// We pull hard: get output on first call
		recv = (Number) p.pullHard();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on first pull, got " + recv);
		}
		recv = (Number) p.pullHard();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on second pull, got " + recv);
		}
	}

	
	@Test
	public void testWindowPush1()
	{
		Number recv;
		QueueSource cs = new QueueSource(1, 1); // Sequence of 1s
		Window wp = new Window(new CumulativeSum(), 3);
		QueueSink qs = new QueueSink(1);
		Connector.connect(cs, wp);
		Connector.connect(wp, qs);
		// We must push three times to get the first output
		cs.push();
		recv = (Number) qs.remove()[0];
		if (recv != null)
		{
			fail("Expected null on first push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove()[0];
		if (recv != null)
		{
			fail("Expected null on second push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove()[0];
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on third push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove()[0];
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on fourth push, got " + recv);
		}
	}
	
	@Test
	public void testDecimatePull1()
	{
		int op_num = 0;
		QueueSource ones = new QueueSource(1, 1);
		CumulativeSum count = new CumulativeSum();
		Connector.connect(ones, count);
		CountDecimate decim = new CountDecimate(2);
		Connector.connect(count, decim);
		QueueSink sink = new QueueSink(1);
		Connector.connect(decim, sink);
		Number recv;
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1 on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv != null)
		{
			fail("Expected null on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv != null)
		{
			fail("Expected null on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 5)
		{
			fail("Expected 5 on pull " + op_num + ", got " + recv);
		}
	}
	
	@Test
	public void testDecimatePush1()
	{
		int op_num = 0;
		QueueSource ones = new QueueSource(1, 1);
		CumulativeSum count = new CumulativeSum();
		Connector.connect(ones, count);
		CountDecimate decim = new CountDecimate(2);
		Connector.connect(count, decim);
		QueueSink sink = new QueueSink(1);
		Connector.connect(decim, sink);
		Number recv;
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1 on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv != null)
		{
			fail("Expected null on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv != null)
		{
			fail("Expected null on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 5)
		{
			fail("Expected 5 on push " + op_num + ", got " + recv);
		}
	}
	
	@Test
	public void testAdditionPush1()
	{
		LinkedList<Object> l_input1 = new LinkedList<Object>();
		l_input1.add(1);
		l_input1.add(2);
		l_input1.add(3);
		LinkedList<Object> l_input2 = new LinkedList<Object>();
		l_input2.add(6);
		l_input2.add(4);
		l_input2.add(0);
		QueueSource input1 = new QueueSource(l_input1, 1);
		QueueSource input2 = new QueueSource(l_input2, 1);
		Function add = new Function(new Addition(2));
		Connector.connect(input1, input2, add);
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
	public void testFilter1()
	{
		LinkedList<Object> l_input1 = new LinkedList<Object>();
		l_input1.add(1);
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		LinkedList<Object> l_input2 = new LinkedList<Object>();
		l_input2.add(true);
		l_input2.add(false);
		l_input2.add(true);
		l_input2.add(false);
		QueueSource input1 = new QueueSource(l_input1, 1);
		QueueSource input2 = new QueueSource(l_input2, 1);
		Filter f = new Filter();
		Connector.connect(input1, input2, f);
		QueueSink sink = new QueueSink(1);
		Connector.connect(f, sink);
		Number recv;
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // 1
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1, got " + recv);
		}
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}
		input1.push();
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // 1
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3, got " + recv);
		}
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}	
	}
	
	@Test
	public void testFilter2()
	{
		LinkedList<Object> l_input1 = new LinkedList<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(6);
		QueueSource input1 = new QueueSource(l_input1, 1);
		Fork fork = new Fork(2);
		Connector.connect(input1, fork);
		Filter filter = new Filter();
		Connector.connect(fork, filter, 0, 0);
		Function even = new Function(new IsEven());
		Connector.connect(fork, even, 1, 0);
		Connector.connect(even, filter, 0, 1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(filter, sink);
		Number recv;
		input1.push();
		recv = (Number) sink.remove()[0]; // 2
		assertEquals(2, recv);
		input1.push();
		recv = (Number) sink.remove()[0]; // null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}
		input1.push();
		input1.push();
		recv = (Number) sink.remove()[0]; // 4
		if (recv == null || recv.intValue() != 4)
		{
			fail("Expected 4, got " + recv);
		}
		recv = (Number) sink.remove()[0]; // 6
		if (recv == null || recv.intValue() != 6)
		{
			fail("Expected 6, got " + recv);
		}
	}
	
	@Test
	public void testGroupPush1()
	{
		// Create the group
		Function add = new Function(new Addition(2));
		GroupProcessor add_plus_10 = new GroupProcessor(2, 1);
		add_plus_10.addProcessor(add);
		add_plus_10.associateInput(0, add, 0);
		add_plus_10.associateInput(1, add, 1);
		add_plus_10.associateOutput(0, add, 0);
		
		// Connect the group to two sources and one sink
		LinkedList<Object> l_input1 = new LinkedList<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(6);
		QueueSource input1 = new QueueSource(l_input1, 1);
		LinkedList<Object> l_input2 = new LinkedList<Object>();
		l_input2.add(1);
		l_input2.add(2);
		l_input2.add(3);
		l_input2.add(4);
		QueueSource input2 = new QueueSource(l_input2, 1);
		Connector.connect(input1, input2, add_plus_10);
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
	public void testBinaryPull()
	{
		QueueSource src_left = new QueueSource(null, 1);
		QueueSource src_right = new QueueSource(null, 1);
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
		Function add = new Function(new Addition(2));
		Connector.connect(src_left, add, 0, 0);
		Connector.connect(src_right, add, 0, 1);
		Pullable p = add.getPullableOutput(0);
		Number n;
		n = (Number) p.pull();
		assertNull(n);
		n = (Number) p.pull();
		assertEquals(11, n.intValue());

	}
	
	@Test
	public void testGroupPull1()
	{
		// Create the group
		Function add = new Function(new Addition(2));
		GroupProcessor add_plus_10 = new GroupProcessor(2, 1);
		add_plus_10.addProcessor(add);
		add_plus_10.associateInput(0, add, 0);
		add_plus_10.associateInput(1, add, 1);
		add_plus_10.associateOutput(0, add, 0);
		
		// Connect the group to two sources and one sink
		LinkedList<Object> l_input1 = new LinkedList<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(6);
		QueueSource input1 = new QueueSource(l_input1, 1);
		LinkedList<Object> l_input2 = new LinkedList<Object>();
		l_input2.add(1);
		l_input2.add(2);
		l_input2.add(3);
		l_input2.add(4);
		QueueSource input2 = new QueueSource(l_input2, 1);
		Connector.connect(input1, input2, add_plus_10);
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
		Function add = new Function(new Addition(2));
		Incrementer inc = new Incrementer(10);
		Connector.connect(inc, add, 0, 0);
		GroupProcessor add_plus_10 = new GroupProcessor(2, 1);
		add_plus_10.addProcessor(add);
		add_plus_10.associateInput(0, inc, 0);
		add_plus_10.associateInput(1, add, 1);
		add_plus_10.associateOutput(0, add, 0);
		
		// Connect the group to two sources and one sink
		LinkedList<Object> l_input1 = new LinkedList<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(6);
		QueueSource input1 = new QueueSource(l_input1, 1);
		LinkedList<Object> l_input2 = new LinkedList<Object>();
		l_input2.add(1);
		l_input2.add(2);
		l_input2.add(3);
		l_input2.add(4);
		QueueSource input2 = new QueueSource(l_input2, 1);
		Connector.connect(input1, input2, add_plus_10);
		QueueSink sink = new QueueSink(1);
		Connector.connect(add_plus_10, sink);
		Number recv, expected;
		
		// Run
		input1.push();
		input2.push();
		expected = 13;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		input1.push();
		input2.push();
		expected = 15;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		input1.push();
		input2.push();
		expected = 17;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
		input1.push();
		input2.push();
		expected = 20;
		recv = (Number) sink.getQueue(0).remove();
		if (recv == null || recv.intValue() != expected.intValue())
		{
			fail("Expected " + expected + ", got " + recv);
		}
	}
	
	@Test
	public void testFork1()
	{
		Vector<Object> events = new Vector<Object>();
		events.add("A");
		events.add("B");
		events.add("C");
		events.add("D");
		QueueSource cp = new QueueSource("", 1);
		cp.setEvents(events);
		Fork f = new Fork(2);
		Connector.connect(cp,  f);
		Pullable p1 = f.getPullableOutput(0);
		Pullable p2 = f.getPullableOutput(1);
		String recv;
		recv = (String) p1.pull();
		assertEquals("A", recv);
		recv = (String) p1.pull();
		assertEquals("B", recv);
		recv = (String) p2.pull();
		assertEquals("A", recv);
		recv = (String) p1.pull();
		assertEquals("C", recv);
		recv = (String) p2.pull();
		assertEquals("B", recv);		
	}
	
	@Test
	public void testFork2()
	{
		Vector<Object> events = new Vector<Object>();
		events.add("A");
		events.add("B");
		events.add("C");
		events.add("D");
		QueueSource cp = new QueueSource("", 1);
		cp.setEvents(events);
		Fork f = new Fork(2);
		Connector.connect(cp,  f);
		Fork new_f = new Fork(3, f);
		Pullable p1 = new_f.getPullableOutput(0);
		Pullable p2 = new_f.getPullableOutput(1);
		Pullable p3 = new_f.getPullableOutput(2);
		String recv;
		recv = (String) p3.pull();
		assertEquals("A", recv);
		recv = (String) p1.pull();
		assertEquals("A", recv);
		recv = (String) p2.pull();
		assertEquals("A", recv);
		recv = (String) p1.pull();
		assertEquals("B", recv);
		recv = (String) p2.pull();
		assertEquals("B", recv);		
	}
	
	@Test
	public void testSmartFork1()
	{
		Vector<Object> events = new Vector<Object>();
		events.add("A");
		events.add("B");
		events.add("C");
		events.add("D");
		QueueSource cp = new QueueSource("", 1);
		cp.setEvents(events);
		SmartFork f = new SmartFork(2);
		Connector.connect(cp,  f);
		Pullable p1 = f.getPullableOutput(0);
		Pullable p2 = f.getPullableOutput(1);
		String recv;
		recv = (String) p1.pull();
		assertEquals("A", recv);
		recv = (String) p1.pull();
		assertEquals("B", recv);
		recv = (String) p2.pull();
		assertEquals("A", recv);
		recv = (String) p1.pull();
		assertEquals("C", recv);
		recv = (String) p2.pull();
		assertEquals("B", recv);		
	}
	
	@Test
	public void testSmartFork2()
	{
		Vector<Object> events = new Vector<Object>();
		events.add("A");
		events.add("B");
		events.add("C");
		events.add("D");
		QueueSource cp = new QueueSource("", 1);
		cp.setEvents(events);
		SmartFork f = new SmartFork(2);
		Connector.connect(cp,  f);
		SmartFork new_f = new SmartFork(3, f);
		Pullable p1 = new_f.getPullableOutput(0);
		Pullable p2 = new_f.getPullableOutput(1);
		Pullable p3 = new_f.getPullableOutput(2);
		String recv;
		recv = (String) p3.pull();
		assertEquals("A", recv);
		recv = (String) p1.pull();
		assertEquals("A", recv);
		recv = (String) p2.pull();
		assertEquals("A", recv);
		recv = (String) p1.pull();
		assertEquals("B", recv);
		recv = (String) p2.pull();
		assertEquals("B", recv);		
	}

	
	/**
	 * This test does not assert anything. It is used for step-by-step debugging
	 * of the {@link SingleProcessor.OutputPullable#hasNext()} method.
	 */
	@Test
	public void testHasNext()
	{
		Vector<Object> events = new Vector<Object>();
		events.add("A");
		events.add("B");
		events.add("C");
		events.add("D");
		QueueSource cp = new QueueSource("", 1);
		cp.setEvents(events);
		Passthrough pt = new Passthrough(1);
		Connector.connect(cp, pt);
		Pullable p = pt.getPullableOutput(0);
		for (int i = 0; i < 10; i++)
		{
			if (p.hasNext() == Pullable.NextStatus.YES)
			{
				p.pull();
			}
		}
		assertTrue(true);
	}
	
	@Test
	public void testMuxerPush1()
	{
		Integer i;
		Multiplexer mux = new Multiplexer(2);
		QueueSink qs = new QueueSink(1);
		Connector.connect(mux, qs);
		Queue<Object> q = qs.getQueue(0);
		Pushable push1 = mux.getPushableInput(0);
		Pushable push2 = mux.getPushableInput(1);
		push1.push(0);
		assertTrue(!q.isEmpty());
		i = (Integer) q.remove();
		assertEquals(0, i.intValue());
		push2.push(1);
		push1.push(2);
		assertTrue(!q.isEmpty());
		i = (Integer) q.remove();
		assertEquals(1, i.intValue());
	}

}
