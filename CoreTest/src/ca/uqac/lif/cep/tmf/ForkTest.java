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
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Utilities;
import ca.uqac.lif.cep.tmf.Fork;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.QueueSourceBatch;

/**
 * Unit tests for {@link Fork}
 * @author Sylvain Hallé
 */
public class ForkTest
{
	@SuppressWarnings("unchecked")
	@Test
	public void testFork() 
	{
		Passthrough p1 = new Passthrough(1);
		Fork fork = new Fork(3);
		Connector.connect(p1, fork);
		Pushable push = p1.getPushableInput(0);
		QueueSink[] sinks = new QueueSink[3];
		Queue<Object>[] queues = new Queue[3];
		for (int i = 0; i < 3; i++)
		{
			sinks[i] = new QueueSink(1);
			Connector.connect(fork, i, sinks[i], 0);
			queues[i] = sinks[i].getQueue(0);
		}
		for (int k = 0; k < 2; k++)
		{
			for (int i = 0; i < 5; i++)
			{
				push.push(i);
				for (int j = 0; j < 2; j++)
				{
					Utilities.queueContains(i, queues[j]);
				}
			}
		}
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testExtendArityFork() 
	{
		Passthrough p1 = new Passthrough(1);
		Fork fork = new Fork(2);
		Connector.connect(p1, fork);
		Pushable push = p1.getPushableInput(0);
		QueueSink[] sinks = new QueueSink[3];
		Queue<Object>[] queues = new Queue[3];
		for (int i = 0; i < 2; i++)
		{
			sinks[i] = new QueueSink(1);
			Connector.connect(fork, i, sinks[i], 0);
			queues[i] = sinks[i].getQueue(0);
		}
		fork.extendOutputArity(3);
		sinks[2] = new QueueSink(1);
		Connector.connect(fork, 2, sinks[2], 0);
		queues[2] = sinks[2].getQueue(0);
		for (int k = 0; k < 2; k++)
		{
			for (int i = 0; i < 5; i++)
			{
				push.push(i);
				for (int j = 0; j < 3; j++)
				{
					Utilities.queueContains(i, queues[j]);
				}
			}
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
		QueueSource cp = new QueueSource(1);
		cp.setEvents(events);
		Fork f = new Fork(2);
		Connector.connect(cp,  f);
		Pullable p1 = f.getPullableOutput(0);
		Pullable p2 = f.getPullableOutput(1);
		String recv;
		recv = (String) p1.pullSoft();
		assertEquals("A", recv);
		recv = (String) p1.pullSoft();
		assertEquals("B", recv);
		recv = (String) p2.pullSoft();
		assertEquals("A", recv);
		recv = (String) p1.pullSoft();
		assertEquals("C", recv);
		recv = (String) p2.pullSoft();
		assertEquals("B", recv);		
	}
	
	@Test
	public void testFork5() 
	{
		/*
		 * In this test, we push events faster than we pull them
		 */
		QueueSourceBatch qsource = new QueueSourceBatch(1);
		Vector<Object> events = new Vector<Object>();
		events.add(0);
		events.add(1);
		events.add(2);
		qsource.setEvents(events);
		Fork fork = new Fork(2);
		Connector.connect(qsource, fork);
		QueueSink qs1 = new QueueSink(1);
		Connector.connect(fork, 0, qs1, 0);
		QueueSink qs2 = new QueueSink(1);
		Connector.connect(fork, 1, qs2, 0);
		Queue<Object> q1 = qs1.getQueue(0);
		Queue<Object> q2 = qs2.getQueue(0);
		qs1.pull();
		Utilities.queueContains(0, q1);
		assertEquals(0, q2.size());
	}
}
