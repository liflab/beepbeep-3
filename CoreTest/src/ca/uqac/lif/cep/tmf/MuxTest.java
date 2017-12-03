/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;

/**
 * Unit tests for the {@link Multiplexer} and {@link Demultiplexer}
 * processors.
 */
public class MuxTest 
{
	@Test
	public void testMuxPush()
	{
		Object out;
		Multiplex mux = new Multiplex(2);
		QueueSink sink = new QueueSink();
		Connector.connect(mux, sink);
		Queue<Object> contents = sink.getQueue();
		Pushable p1 = mux.getPushableInput(0);
		Pushable p2 = mux.getPushableInput(1);
		p1.push("foo");
		p2.push(3);
		out = contents.poll();
		assertEquals("foo", out);
		out = contents.poll();
		assertEquals(3, ((Integer) out).intValue());
		p1.push("bar");
		p1.push("baz");
		p2.push(5);
		out = contents.poll();
		assertEquals("bar", out);
		out = contents.poll();
		assertEquals("baz", out);
		out = contents.poll();
		assertEquals(5, ((Integer) out).intValue());
		// These methods should not do anything
		p2.dispose();
		assertEquals(1, p2.getPosition());
		assertEquals(mux, p2.getProcessor());
	}
	
	@Test
	public void testMuxPull()
	{
		QueueSource s1 = new QueueSource().setEvents("foo", "bar", "baz");
		QueueSource s2 = new QueueSource().setEvents(1, 2, 3);
		Multiplex mux = new Multiplex(2);
		Connector.connect(s1, 0, mux, 0);
		Connector.connect(s2, 0, mux, 1);
		Pullable p = mux.getPullableOutput();
		assertEquals("foo", p.pull());
		assertEquals(1, ((Integer) p.pull()).intValue());
		assertEquals("bar", p.pull());
		assertEquals(2, ((Integer) p.pull()).intValue());
		assertEquals("baz", p.pull());
		assertEquals(3, ((Integer) p.pull()).intValue());
		// These methods should not do anything
		p.start();
		p.stop();
		p.dispose();
		assertEquals(p, p.iterator());
		assertEquals(0, p.getPosition());
		assertEquals(mux, p.getProcessor());
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
	}
}
