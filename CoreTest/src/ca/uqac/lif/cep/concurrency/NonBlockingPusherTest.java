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
package ca.uqac.lif.cep.concurrency;

import static org.junit.Assert.*;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.concurrency.ThreadPullableTest.DelayProcessor;
import ca.uqac.lif.cep.tmf.QueueSink;

public class NonBlockingPusherTest 
{
	@Test
	public void testPushableWithoutThreads1() throws ConnectorException
	{
		int max_procs = 5;
		ThreadManager tm = new ThreadManager(0); // No threads
		NonBlockingPusher[] procs = new NonBlockingPusher[max_procs];
		QueueSink[] sinks = new QueueSink[max_procs];
		@SuppressWarnings("unchecked")
		Queue<Object>[] queues = new Queue[max_procs];
		for (int i = 0; i < max_procs; i++)
		{
			procs[i] = new NonBlockingPusher(new DelayProcessor(1, 1000), tm);
			procs[i].start();
			sinks[i] = new QueueSink();
			Connector.connect(procs[i], sinks[i]);
			queues[i] = sinks[i].getQueue();
		}
		long first_time = System.currentTimeMillis();
		long last_time = System.currentTimeMillis();
		for (int i = 0; i < max_procs; i++)
		{
			System.out.println("Pushing to " + i);
			Pushable p = procs[i].getPushableInput();
			//System.out.println(p);
			p.pushFast(i);
			p.dispose();
		}
		for (int i = 0; i < max_procs; i++)
		{
			procs[i].getPushableInput().waitFor();
			long this_time = System.currentTimeMillis();
			//long elapsed = this_time - last_time;
			last_time = this_time;
			assertFalse(queues[i].isEmpty());
			Object o = queues[i].poll();
			assertTrue(o instanceof Number);
			System.out.println(i + ":" + o);
			//assertEquals(i, ((Number) o).intValue());
			//System.out.println(elapsed);
		}
		System.out.println("Total duration: " + (last_time - first_time));
	}
	
	@Test
	public void testPushableWithOneThread1() throws ConnectorException
	{
		int max_procs = 5;
		ThreadManager tm = new ThreadManager(1); // 1 thread
		NonBlockingPusher[] procs = new NonBlockingPusher[max_procs];
		QueueSink[] sinks = new QueueSink[max_procs];
		@SuppressWarnings("unchecked")
		Queue<Object>[] queues = new Queue[max_procs];
		for (int i = 0; i < max_procs; i++)
		{
			procs[i] = new NonBlockingPusher(new DelayProcessor(1, 1000), tm);
			procs[i].start();
			sinks[i] = new QueueSink();
			Connector.connect(procs[i], sinks[i]);
			queues[i] = sinks[i].getQueue();
		}
		long first_time = System.currentTimeMillis();
		long last_time = System.currentTimeMillis();
		for (int i = 0; i < max_procs; i++)
		{
			System.out.println("Pushing to " + i);
			Pushable p = procs[i].getPushableInput();
			//System.out.println(p);
			p.pushFast(i);
			p.dispose();
		}
		for (int i = 0; i < max_procs; i++)
		{
			procs[i].getPushableInput().waitFor();
			long this_time = System.currentTimeMillis();
			//long elapsed = this_time - last_time;
			last_time = this_time;
			assertFalse(queues[i].isEmpty());
			Object o = queues[i].poll();
			assertTrue(o instanceof Number);
			System.out.println(i + ":" + o);
			//assertEquals(i, ((Number) o).intValue());
			//System.out.println(elapsed);
		}
		System.out.println("Total duration: " + (last_time - first_time));
	}
	
	@Test
	public void testPushableWithOneThread2() throws ConnectorException
	{
		int max_procs = 5;
		ThreadManager tm = new ThreadManager(1); // 1 thread
		NonBlockingPusher[] procs = new NonBlockingPusher[max_procs];
		QueueSink[] sinks = new QueueSink[max_procs];
		@SuppressWarnings("unchecked")
		Queue<Object>[] queues = new Queue[max_procs];
		for (int i = 0; i < max_procs; i++)
		{
			procs[i] = new NonBlockingPusher(new DelayProcessor(1, 1000), tm);
			procs[i].start();
			sinks[i] = new QueueSink();
			Connector.connect(procs[i], sinks[i]);
			queues[i] = sinks[i].getQueue();
		}
		long first_time = System.currentTimeMillis();
		long last_time = System.currentTimeMillis();
		for (int i = 0; i < max_procs; i++)
		{
			System.out.println("Pushing to " + i);
			Pushable p = procs[i].getPushableInput();
			//System.out.println(p);
			p.pushFast(i);
		}
		for (int i = 0; i < max_procs; i++)
		{
			Pushable p = procs[i].getPushableInput();
			p.dispose();
			p.waitFor();
			long this_time = System.currentTimeMillis();
			//long elapsed = this_time - last_time;
			last_time = this_time;
			assertFalse(queues[i].isEmpty());
			Object o = queues[i].poll();
			assertTrue(o instanceof Number);
			System.out.println(i + ":" + o);
			//assertEquals(i, ((Number) o).intValue());
			//System.out.println(elapsed);
		}
		System.out.println("Total duration: " + (last_time - first_time));
	}

}
