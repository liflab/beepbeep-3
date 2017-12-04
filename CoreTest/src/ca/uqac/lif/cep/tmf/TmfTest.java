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

import static org.junit.Assert.*;

import java.util.Queue;
import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.NextStatus;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Utilities;
import ca.uqac.lif.cep.functions.StreamVariable;
import ca.uqac.lif.cep.functions.Constant;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.tmf.CountDecimate;
import ca.uqac.lif.cep.tmf.Filter;
import ca.uqac.lif.cep.tmf.Freeze;
import ca.uqac.lif.cep.tmf.Insert;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.Prefix;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.SinkLast;
import ca.uqac.lif.cep.tmf.Trim;
import ca.uqac.lif.cep.tmf.Window;
import ca.uqac.lif.cep.util.Numbers;

/**
 * Unit tests for classes of the TMF package.
 * @author Sylvain Hallé
 */
public class TmfTest
{
	@Test
	public void testReplace()
	{
		ReplaceWith rw = new ReplaceWith(10);
		QueueSink sink = new QueueSink();
		Queue<Object> q = sink.getQueue();
		Connector.connect(rw, sink);
		Pushable p = rw.getPushableInput();
		p.push("foo");
		assertEquals(10, ((Integer) q.poll()).intValue());
		p.push("bar");
		assertEquals(10, ((Integer) q.poll()).intValue());
		rw = rw.duplicate();
		p.push("foo");
		assertEquals(10, ((Integer) q.poll()).intValue());
		p.push("bar");
		assertEquals(10, ((Integer) q.poll()).intValue());
	}

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

	@Test(timeout=1000)
	public void testPump()
	{
		QueueSource qs = new QueueSource().setEvents(1, 2, 3, 4);
		qs.loop(false);
		Pump pump = new Pump();
		Connector.connect(qs, pump);
		QueueSink sink = new QueueSink();
		Connector.connect(pump, sink);
		pump.run();
		Queue<Object> q = sink.getQueue();
		assertEquals(4, q.size());
	}

	@Test(timeout=2000)
	public void testPumpStop1() throws InterruptedException
	{
		QueueSource qs = new QueueSource().setEvents(1, 2, 3, 4);
		qs.loop(true);
		Pump pump = new Pump(50);
		Connector.connect(qs, pump);
		QueueSink sink = new QueueSink();
		Connector.connect(pump, sink);
		Thread th = new Thread(pump);
		th.start();
		Thread.sleep(300);
		pump.stop();
		Thread.sleep(100);
		assertFalse(th.isAlive());
		Queue<Object> q = sink.getQueue();
		assertTrue(q.size() > 4);
	}

	@Test(timeout=2000)
	public void testPumpStop2() throws InterruptedException
	{
		QueueSource qs = new QueueSource().setEvents(1, 2, 3, 4);
		qs.loop(true);
		Pump pump = new Pump(50);
		Connector.connect(qs, pump);
		QueueSink sink = new QueueSink();
		Connector.connect(pump, sink);
		pump.start();
		Thread.sleep(300);
		pump.stop();
		Thread.sleep(100);
		Queue<Object> q = sink.getQueue();
		assertTrue(q.size() > 4);
	}

	@Test
	public void testTank()
	{
		Tank t = new Tank();
		Pushable ps = t.getPushableInput();
		Pullable pl = t.getPullableOutput();
		ps.push("foo");
		ps.push("bar");
		assertTrue(pl.hasNext());
		assertEquals("foo", pl.pull());
		assertTrue(pl.hasNext());
		assertEquals("bar", pl.pull());
		assertFalse(pl.hasNext());
		assertEquals(NextStatus.MAYBE, pl.hasNextSoft());
		ps.push("baz");
		assertEquals(NextStatus.YES, pl.hasNextSoft());
		assertTrue(pl.hasNext());
		assertEquals("baz", pl.pull());
		assertTrue(pl == pl.iterator());
		assertEquals(0, pl.getPosition());
		assertEquals(0, ps.getPosition());
		assertEquals(t, pl.getProcessor());
		assertEquals(t, ps.getProcessor());
		// These methods should all do nothing
		ps.dispose();
		pl.dispose();
		pl.start();
		pl.stop();
	}

	@Test
	public void testTankLast()
	{
		TankLast t = new TankLast();
		Pushable ps = t.getPushableInput();
		Pullable pl = t.getPullableOutput();
		ps.push("foo");
		ps.push("bar");
		assertTrue(pl.hasNext());
		assertEquals("bar", pl.pull());
		assertFalse(pl.hasNext());
		assertEquals(NextStatus.MAYBE, pl.hasNextSoft());
		ps.push("baz");
		assertTrue(pl.hasNext());
		assertEquals("baz", pl.pull());
		assertTrue(pl == pl.iterator());
		assertEquals(0, pl.getPosition());
		assertEquals(0, ps.getPosition());
		assertEquals(t, pl.getProcessor());
		assertEquals(t, ps.getProcessor());
		// These methods should all do nothing
		ps.dispose();
		pl.dispose();
		pl.start();
		pl.stop();
	}

	@Test(timeout=1000)
	public void testTimeDecimate() throws InterruptedException
	{
		QueueSource source = new QueueSource().setEvents(0);
		TimeDecimate td = new TimeDecimate(200);
		Connector.connect(source, td);
		Pullable p = td.getPullableOutput();
		long before = System.currentTimeMillis();
		assertTrue(p.hasNext());
		p.pull();
		while (p.hasNextSoft() != NextStatus.YES)
		{
			Thread.sleep(10);
		}
		long after = System.currentTimeMillis();
		assertTrue(after - before > 200);
		td = td.duplicate();
		assertEquals(200, td.getInterval());
	}

	@Test(timeout=1000)
	public void testTimeDecimateReset() throws InterruptedException
	{
		QueueSource source = new QueueSource().setEvents(0);
		TimeDecimate td = new TimeDecimate(20000);
		Connector.connect(source, td);
		Pullable p = td.getPullableOutput();
		assertTrue(p.hasNext());
		p.pull();
		for (int i = 0; i < 10; i++)
		{
			assertEquals(NextStatus.MAYBE, p.hasNextSoft());
			Thread.sleep(10);
		}
		td.reset();
		assertEquals(NextStatus.YES, p.hasNextSoft());
	}

	@Test
	public void testSimpleFilter()
	{
		QueueSource source = new QueueSource().setEvents(2, 3, 5, 6, 8);
		SimpleFilter filter = new SimpleFilter(Numbers.isEven);
		Connector.connect(source, filter);
		Pullable p = filter.getPullableOutput();
		assertEquals(2, p.pull());
		assertEquals(6, p.pull());
		assertEquals(8, p.pull());
		SimpleFilter filter2 = filter.duplicate();
		assertEquals(Numbers.isEven, filter2.getCondition());
	}

	@Test
	public void testSimpleFilterClone()
	{
		FunctionTree ft = new FunctionTree(Numbers.isGreaterThan, new StreamVariable(0), new Constant(4));
		SimpleFilter filter = new SimpleFilter(ft);
		SimpleFilter filter2 = filter.duplicate();
		Function f = filter2.getCondition();
		assertFalse(f == ft);
		assertTrue(f instanceof FunctionTree);
		Object[] out = new Object[1];
		f.evaluate(new Object[]{6}, out);
		assertEquals(true, out[0]);
		f.evaluate(new Object[]{3}, out);
		assertEquals(false, out[0]);
	}
}
