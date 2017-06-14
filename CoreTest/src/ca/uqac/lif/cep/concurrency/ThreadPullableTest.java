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
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SingleProcessor;

public class ThreadPullableTest 
{
	/* Test with a small number, just to make sure the computation is OK */
	
	@Test(timeout=2000)
	public void testContinuousPullWithThreads()
	{
		ThreadManager tm = new ThreadManager(-1); // Unlimited threads
		DelayProcessor fp = new DelayProcessor(0, 200);
		Pullable f_pull = fp.getPullableOutput();
		Pullable t_pull = ThreadPullable.tryPullable(f_pull, tm);
		assertTrue(t_pull instanceof ThreadPullable);
		t_pull.start();
		Integer bi = (Integer) t_pull.pull();
		assertNotNull(bi);
		t_pull.stop();
	}
	
	@Test(timeout=2000)
	public void testContinuousPullWithoutThreads()
	{
		ThreadManager tm = new ThreadManager(0); // No thread
		DelayProcessor fp = new DelayProcessor(0, 200);
		Pullable f_pull = fp.getPullableOutput();
		Pullable t_pull = ThreadPullable.tryPullable(f_pull, tm);
		assertFalse(t_pull instanceof ThreadPullable);
		t_pull.start();
		Integer bi = (Integer) t_pull.pull();
		assertNotNull(bi);
		t_pull.stop();
	}
	
	/**
	 * Two processors are chained. Each takes 500 ms to produce each event.
	 * Therefore, each event takes 500 + 500 ms before being output: processor
	 * A first produces its output in 500 ms, which is then passed to
	 * processor B that takes another 500 ms to create its output. Since
	 * A and B are in the same thread, both cannot work at the same time.
	 */
	@Test(timeout=2000)
	public void testSequentialChain1()
	{
		DelayProcessor delay_1 = new DelayProcessor(0, 500);
		Pullable d1_pull = delay_1.getPullableOutput();
		DelayProcessor delay_2 = new DelayProcessor(1, 500);
		delay_2.setPullableInput(0, d1_pull);
		Pullable d2_pull = delay_2.getPullableOutput();
		long last_time = System.currentTimeMillis();
		for (int num_events = 0; num_events < 5; num_events++)
		{
			Object o = d2_pull.pull();
			assertNotNull(o);
			long this_time = System.currentTimeMillis();
			float duration = (float) (this_time - last_time); 
			assertEquals(1000f, duration, 100f);
			last_time = this_time;
		}
	}

	/**
	 * Two processors are chained like in {@link #testSequentialChain1()},
	 * but this time, a ThreadPullable is applied
	 * to the output of the first. This has for effect that A now works in
	 * a separate thread than B. In the first 500 ms, A produces its first
	 * event and sends it to B; in the next 500 ms, B processes A's output,
	 * and at the same time, A produces a second event. The end result is
	 * that the first output event takes 1 s to be produced, but all the
	 * others now only take 500 ms. The chain works twice as fast.  
	 */
	@Test(timeout=10000)
	public void testContinuousChain1()
	{
		ThreadManager tm = new ThreadManager(-1);
		DelayProcessor delay_1 = new DelayProcessor(0, 500);
		Pullable d1_pull = delay_1.getPullableOutput();
		Pullable d1_tpull = ThreadPullable.tryPullable(d1_pull, tm);
		assertTrue(d1_tpull instanceof ThreadPullable);
		DelayProcessor delay_2 = new DelayProcessor(1, 500);
		delay_2.setPullableInput(0, d1_tpull);
		Pullable d2_pull = delay_2.getPullableOutput();
		d1_tpull.start();
		long last_time = System.currentTimeMillis();
		boolean first = true;
		for (int num_events = 0; num_events < 5; num_events++)
		{
			Object o = d2_pull.pull();
			assertNotNull(o);
			long this_time = System.currentTimeMillis();
			float duration = (float) (this_time - last_time);
			if (first)
			{
				first = false;
				assertTrue(duration > 1000);
			}
			else
			{
				// We record less than 1 sec, meaning that the two
				// processors have worked in parallel. This should be
				// around 500 ms, but it fluctuates due to the precision
				// of the timer
				assertTrue(duration < 800);
			}
			last_time = this_time;
		}
	}
	
	/**
	 * Same as {@link #testContinuousChain1()}, but with the processor
	 * encased in a GroupProcessor.
	 * @throws ConnectorException 
	 */
	@Test(timeout=10000)
	public void testContinuousGroup1() throws ConnectorException
	{
		DelayProcessor delay_1 = new DelayProcessor(0, 500);
		PullThreadGroup group = new PullThreadGroup(0, 1);
		group.addProcessor(delay_1);
		group.associateOutput(0, delay_1, 0);
		DelayProcessor delay_2 = new DelayProcessor(1, 500);
		Connector.connect(group, delay_2);
		Pullable d2_pull = delay_2.getPullableOutput();
		group.start();
		boolean first = true;
		long last_time = System.currentTimeMillis();
		for (int num_events = 0; num_events < 5; num_events++)
		{
			Object o = d2_pull.pull();
			assertNotNull(o);
			long this_time = System.currentTimeMillis();
			float duration = (float) (this_time - last_time);
			if (first)
			{
				first = false;
				assertTrue(duration > 1000);
			}
			else
			{
				// We record less than 1 sec, meaning that the two
				// processors have worked in parallel. This should be
				// around 500 ms, but it fluctuates due to the precision
				// of the timer
				assertTrue(duration < 800);
			}
			System.out.println(duration);
			last_time = this_time;
		}
		group.stop();
	}
	
	/**
	 * Processor that simulates a long computation by waiting
	 */
	public static class DelayProcessor extends SingleProcessor
	{
		protected final long m_waitInterval;
		
		public DelayProcessor(int in_arity, long wait_interval)
		{
			super(in_arity, 1);
			m_waitInterval = wait_interval;
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
		{
			try 
			{
				Thread.sleep(m_waitInterval);
			} 
			catch (InterruptedException e) 
			{
				// Do nothing
			}
			if (getInputArity() == 0)
			{
				return true;
			}
			outputs.add(inputs);
			return true;
		}

		@Override
		public DelayProcessor clone() 
		{
			return new DelayProcessor(getInputArity(), m_waitInterval);
		}
		
	}
}
