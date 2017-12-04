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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Queue;
import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.tmf.Multiplex;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the {@link Multiplex} class
 * @author Sylvain Hallé
 */
public class MultiplexerTest 
{
	@Test
	public void testMuxerPush1() 
	{
		Integer i;
		Multiplex mux = new Multiplex(2);
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
	
	@Test
	public void testMultiplexerPush() 
	{
		Multiplex mux = new Multiplex(2);
		Pushable push1 = mux.getPushableInput(0);
		Pushable push2 = mux.getPushableInput(1);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(mux, qsink);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qsink.getQueue(0);
			push1.push(0);
			Utilities.queueContains(0, queue);
			push2.push(100);
			Utilities.queueContains(100, queue);
			push1.push(1);
			push2.push(101);
			assertEquals(2, queue.size());
			int i = ((Number) queue.remove()).intValue();
			assertEquals(1, i);
			Utilities.queueContains(101, queue);
			mux.reset();
			qsink.reset();
		}
	}
	
	@Test
	public void testMultiplexerPull() 
	{
		int i = -1;
		QueueSource qsource1 = new QueueSource(1);
		{
			Vector<Object> contents = new Vector<Object>();
			contents.add(0);
			contents.add(null);
			contents.add(1);
			qsource1.setEvents(contents);
		}
		QueueSource qsource2 = new QueueSource(1);
		{
			Vector<Object> contents = new Vector<Object>();
			contents.add(null);
			contents.add(100);
			contents.add(101);
			qsource2.setEvents(contents);
		}
		Multiplex mux = new Multiplex(2);
		Connector.connect(qsource1, 0, mux, 0);
		Connector.connect(qsource2, 0, mux, 1);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(mux, qsink);
		Queue<Object> queue = qsink.getQueue(0);
		Pullable pull1 = mux.getPullableOutput(0);
		assertEquals(NextStatus.YES, pull1.hasNextSoft());
		qsink.pull();
		assertEquals(1, queue.size());
		i = ((Number) queue.remove()).intValue();
		assertEquals(0, i);
		qsink.pull();
		assertEquals(1, queue.size());
		i = ((Number) queue.remove()).intValue();
		assertEquals(100, i);
		qsink.pull();
		assertEquals(1, queue.size());
		i = ((Number) queue.remove()).intValue();
		assertTrue(i == 101 || i == 1);
		qsink.pull();
		assertEquals(1, queue.size());
		i = ((Number) queue.remove()).intValue();
		assertTrue(i == 101 || i == 1);
	}
	
	@Test
	public void testMultiplexerPullHard() 
	{
		int i = -1;
		QueueSource qsource1 = new QueueSource(1);
		{
			Vector<Object> contents = new Vector<Object>();
			contents.add(0);
			contents.add(null);
			contents.add(1);
			qsource1.setEvents(contents);
		}
		QueueSource qsource2 = new QueueSource(1);
		{
			Vector<Object> contents = new Vector<Object>();
			contents.add(null);
			contents.add(100);
			contents.add(101);
			qsource2.setEvents(contents);
		}
		Multiplex mux = new Multiplex(2);
		Connector.connect(qsource1, 0, mux, 0);
		Connector.connect(qsource2, 0, mux, 1);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(mux, qsink);
		Queue<Object> queue = qsink.getQueue(0);
		Pullable pull1 = mux.getPullableOutput(0);
		assertTrue(pull1.hasNext());
		qsink.pullHard();
		i = ((Number) queue.remove()).intValue();
		assertEquals(0, i);
		qsink.pullHard();
		i = ((Number) queue.remove()).intValue();
		assertEquals(100, i);
		qsink.pullHard();
		i = ((Number) queue.remove()).intValue();
		assertTrue(i == 101 || i == 1);
		qsink.pullHard();
		i = ((Number) queue.remove()).intValue();
		assertTrue(i == 101 || i == 1);
	}
}
