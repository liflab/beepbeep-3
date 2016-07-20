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

import static org.junit.Assert.assertTrue;

import java.util.Queue;
import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.epl.QueueSource;
import ca.uqac.lif.cep.epl.Window;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.CumulativeProcessor;
import ca.uqac.lif.cep.numbers.Addition;

public class ThroughputTest extends BeepBeepUnitTest
{
	/**
	 * Tests the throughput of 10 passthrough processors connected to a source
	 * on 1,000,000 events.
	 */
	@Test
	public void testPassthroughPull() throws ConnectorException
	{
		long num_events = 1000000;
		Vector<Object> events = new Vector<Object>();
		events.add("A");
		events.add("B");
		events.add("C");
		events.add("D");
		QueueSource cp = new QueueSource(null, 1);
		cp.setEvents(events);
		Passthrough pt = new Passthrough(1);
		Connector.connect(cp, pt);
		for (int i = 0; i < 10; i++)
		{
			Passthrough pt2 = new Passthrough(1);
			Connector.connect(pt, pt2);
			pt = pt2;
		}
		Pullable p = pt.getPullableOutput(0);
		float start_time = System.nanoTime();
		for (long n = 0; n < num_events; n++)
		{
			p.hasNext();
			p.pull();
		}
		float end_time = System.nanoTime();
		long throughput = (long) (((float) num_events) / (end_time - start_time) * 1000000000f);
		System.out.println("Throughput on passthrough (pull): " + throughput + " ev/s");
		assertTrue(true);
	}
	
	@Test
	public void testPassthroughPush() throws ConnectorException
	{
		long num_events = 1000000;
		Vector<Object> events = new Vector<Object>();
		events.add("A");
		events.add("B");
		events.add("C");
		events.add("D");
		QueueSource cp = new QueueSource(null, 1);
		cp.setEvents(events);
		Passthrough pt = new Passthrough(1);
		Connector.connect(cp, pt);
		for (int i = 0; i < 10; i++)
		{
			Passthrough pt2 = new Passthrough(1);
			Connector.connect(pt, pt2);
			pt = pt2;
		}
		QueueSink s = new QueueSink(1);
		Connector.connect(pt, s);
		Queue<Object> q = s.getQueue(0);
		float start_time = System.nanoTime();
		for (long n = 0; n < num_events; n++)
		{
			cp.push();
			q.poll();
		}
		float end_time = System.nanoTime();
		long throughput = (long) (((float) num_events) / (end_time - start_time) * 1000000000f);
		System.out.println("Throughput on passthrough (push): " + throughput + " ev/s");
		assertTrue(true);
	}
	
	@Test
	public void testWindow() throws ConnectorException
	{
		long num_events = 1000000;
		Vector<Object> events = new Vector<Object>();
		events.add(1);
		events.add(2);
		events.add(3);
		events.add(4);
		QueueSource cp = new QueueSource(null, 1);
		cp.setEvents(events);
		Window wp = new Window(new Sum(), 3);
		QueueSink qs = new QueueSink(1);
		Connector.connect(cp, wp);
		Connector.connect(wp, qs);
		Queue<Object> q = qs.getQueue(0);
		float start_time = System.nanoTime();
		for (long n = 0; n < num_events; n++)
		{
			cp.push();
			q.poll();
		}
		float end_time = System.nanoTime();
		long throughput = (long) (((float) num_events) / (end_time - start_time) * 1000000000f);
		System.out.println("Throughput on window (push): " + throughput + " ev/s");
		assertTrue(true);
	}
	
	public static class Sum extends CumulativeProcessor
	{
		@SuppressWarnings({ "rawtypes", "unchecked" })
		public Sum()
		{
			super(new CumulativeFunction(Addition.instance));
		}
	}

}
