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
package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Queue;
import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Utilities;

/**
 * Unit tests for classes of the TMF package.
 * @author Sylvain Hallé
 */
public class TmfTest extends BeepBeepUnitTest 
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
	public void testFilter() 
	{
		Filter f = new Filter();
		QueueSink qs = new QueueSink(1);
		Connector.connect(f, qs);
		Pushable in = f.getPushableInput(0);
		Pushable condition = f.getPushableInput(1);
		Queue<Object> queue = qs.getQueue(0);
		for (int k = 0; k < 2; k++)
		{
			in.push(0); condition.push(false);
			assertTrue(queue.isEmpty());
			in.push(1); condition.push(true);
			Utilities.queueContains(1, queue);
			f.reset();
		}
	}

	@Test
	public void testCountDecimate1() 
	{
		CountDecimate f = new CountDecimate(3);
		QueueSink qs = new QueueSink(1);
		Connector.connect(f, qs);
		Pushable in = f.getPushableInput(0);
		Queue<Object> queue = qs.getQueue(0);
		for (int k = 0; k < 2; k++)
		{
			in.push(0);
			assertEquals(1, queue.size());
			Utilities.queueContains(0, queue);
			in.push(1);
			assertTrue(queue.isEmpty());
			in.push(2);
			assertTrue(queue.isEmpty());
			in.push(3);
			Utilities.queueContains(3, queue);
			in.push(4);
			assertTrue(queue.isEmpty());
			in.push(5);
			assertTrue(queue.isEmpty());
			in.push(6);
			Utilities.queueContains(6, queue);
			f.reset();
		}
	}

	@Test
	public void testCountDecimate2() 
	{
		CountDecimate f = new CountDecimate();
		QueueSink qs = new QueueSink(1);
		Connector.connect(f, qs);
		Pushable in = f.getPushableInput(0);
		Queue<Object> queue = qs.getQueue(0);
		for (int k = 0; k < 2; k++)
		{
			in.push(0);
			assertEquals(1, queue.size());
			Utilities.queueContains(0, queue);
			in.push(1);
			Utilities.queueContains(1, queue);
			in.push(2);
			Utilities.queueContains(2, queue);
			f.reset();
		}
	}

	@Test
	public void testFreeze() 
	{
		Freeze f = new Freeze();
		QueueSink qs = new QueueSink(1);
		Connector.connect(f, qs);
		Pushable in = f.getPushableInput(0);
		Queue<Object> queue = qs.getQueue(0);
		for (int k = 0; k < 2; k++)
		{
			in.push(0);
			Utilities.queueContains(0, queue);
			in.push(1);
			Utilities.queueContains(0, queue);
			in.push(2);
			Utilities.queueContains(0, queue);
			f.reset();
		}
	}

	@Test
	public void testPrefix1() 
	{
		Prefix f = new Prefix(3);
		QueueSink qs = new QueueSink(1);
		Connector.connect(f, qs);
		Pushable in = f.getPushableInput(0);
		Queue<Object> queue = qs.getQueue(0);
		for (int k = 0; k < 2; k++)
		{
			in.push(0);
			Utilities.queueContains(0, queue);
			in.push(1);
			Utilities.queueContains(1, queue);
			in.push(2);
			Utilities.queueContains(2, queue);
			in.push(3);
			assertTrue(queue.isEmpty());
			in.push(4);
			assertTrue(queue.isEmpty());
			in.push(5);
			assertTrue(queue.isEmpty());
			f.reset();
		}
	}

	@Test
	public void testQueueSource1() 
	{
		Object o = null;
		QueueSource source = new QueueSource();
		source.addEvent(0);
		Pullable out = source.getPullableOutput(0);
		o = out.pullSoft();
		Utilities.assertEquals(0, o);
		o = out.pullSoft();
		Utilities.assertEquals(0, o);
		o = out.pullSoft();
		Utilities.assertEquals(0, o);
	}

	@Test
	public void testQueueSource2() 
	{
		Object o = null;
		Vector<Object> queue = new Vector<Object>();
		queue.add(0);
		queue.add(1);
		queue.add(2);
		QueueSource source = new QueueSource(1);
		source.setEvents(queue);
		Pullable out = source.getPullableOutput(0);
		for (int i = 0; i < 10; i++)
		{
			o = out.pullSoft();
			assertTrue(o instanceof Integer);
			Utilities.assertEquals(i % 3, o);
		}
	}

	@Test
	public void testQueueSource3() 
	{
		Vector<Object> queue = new Vector<Object>();
		queue.add(0);
		queue.add(1);
		queue.add(2);
		QueueSource source = new QueueSource(1);
		source.setEvents(queue);
		QueueSink sink = new QueueSink(1);
		Connector.connect(source, sink);
		Queue<Object> out = sink.getQueue(0);
		for (int i = 0; i < 10; i++)
		{
			source.push();
			Utilities.queueContains(i % 3, out);
		}
	}

	@Test
	public void testSinkLast() 
	{
		Vector<Object> queue = new Vector<Object>();
		queue.add(0);
		queue.add(1);
		queue.add(2);
		QueueSource source = new QueueSource(1);
		source.setEvents(queue);
		SinkLast sink = new SinkLast(1);
		Connector.connect(source, sink);
		for (int i = 0; i < 10; i++)
		{
			source.push();
			Object[] objs = sink.getLast();
			assertEquals(1, objs.length);
			Utilities.assertEquals(i % 3, objs[0]);
		}
	}

	@Test
	public void testQueueSink1() 
	{
		Object[] o = null;
		QueueSink sink = new QueueSink(2);
		Pushable in1 = sink.getPushableInput(0);
		Pushable in2 = sink.getPushableInput(1);
		in1.push(0);
		o = sink.remove();
		//assertNull(o);
		in2.push("A");
		in1.push(1);
		in2.push("B");
		o = sink.remove();
		assertNotNull(o);
		assertEquals(0, o[0]);
		assertEquals("A", o[1]);
	}

	@Test
	public void testQueueSink2() 
	{
		Vector<Object> queue = new Vector<Object>();
		queue.add(0);
		queue.add(1);
		queue.add(2);
		QueueSource source = new QueueSource(1);
		source.setEvents(queue);
		SinkLast sink = new SinkLast(1);
		Connector.connect(source, sink);
		for (int i = 0; i < 10; i++)
		{
			sink.pull();
			Object[] objs = sink.getLast();
			assertEquals(1, objs.length);
			
			Utilities.assertEquals(i % 3, objs[0]);
		}
	}

	@Test
	public void testQueueSink3() 
	{
		Vector<Object> queue = new Vector<Object>();
		queue.add(0);
		queue.add(1);
		queue.add(2);
		QueueSource source = new QueueSource(1);
		source.setEvents(queue);
		SinkLast sink = new SinkLast();
		Connector.connect(source, sink);
		for (int i = 0; i < 10; i++)
		{
			sink.pullHard();
			Object[] objs = sink.getLast();
			assertEquals(1, objs.length);
			Utilities.assertEquals(i % 3, objs[0]);
		}
	}


	@Test
	public void testWindow1() 
	{
		Passthrough p = new Passthrough(1);
		Window w = new Window(p, 3);
		QueueSink qs = new QueueSink(1);
		Connector.connect(w, qs);
		Pushable in = w.getPushableInput(0);
		Queue<Object> queue = qs.getQueue(0);
		in.push(0);
		assertTrue(queue.isEmpty());
		in.push(1);
		assertTrue(queue.isEmpty());
		in.push(2);
		Utilities.queueContains(2, queue);
		in.push(3);
		Utilities.queueContains(3, queue);
		in.push(4);
		Utilities.queueContains(4, queue);
	}

	@Test
	public void testInsert() 
	{
		Object[] to_insert = {99};
		Insert ins = new Insert(to_insert, 3);
		QueueSink sink = new QueueSink(1);
		Connector.connect(ins, sink);
		Pushable in = ins.getPushableInput(0);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = sink.getQueue(0);
			in.push(0);
			int i = ((Number) queue.remove()).intValue();
			assertEquals(99, i);
			in.push(1);
			i = ((Number) queue.remove()).intValue();
			assertEquals(99, i);
			in.push(2);
			i = ((Number) queue.remove()).intValue();
			assertEquals(99, i);
			in.push(3);
			i = ((Number) queue.remove()).intValue();
			assertEquals(0, i);
			in.push(4);
			i = ((Number) queue.remove()).intValue();
			assertEquals(1, i);
			in.push(5);
			i = ((Number) queue.remove()).intValue();
			assertEquals(2, i);
			ins.reset();
			sink.reset();
		}
	}
}
