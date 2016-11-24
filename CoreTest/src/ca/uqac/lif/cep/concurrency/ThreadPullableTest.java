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

import java.math.BigInteger;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SingleProcessor;

public class ThreadPullableTest 
{
	/* Test with a small number, just to make sure the computation is OK */
	@Test
	public void testOnDemand1()
	{
		FibonacciProcessor fp = new FibonacciProcessor(4);
		Pullable f_pull = fp.getPullableOutput();
		ThreadPullable t_pull = new ThreadPullable(new OnDemandPoller(f_pull));
		t_pull.start();
		BigInteger bi = (BigInteger) t_pull.pull();
		assertNotNull(bi);
		assertEquals(3, bi.intValue());
		t_pull.stop();
	}
	
	@Test
	public void testOnDemand2()
	{
		FibonacciProcessor fp = new FibonacciProcessor(100);
		Pullable f_pull = fp.getPullableOutput();
		ThreadPullable t_pull = new ThreadPullable(new OnDemandPoller(f_pull));
		t_pull.start();
		BigInteger bi = (BigInteger) t_pull.pull();
		assertNotNull(bi);
		t_pull.stop();
	}
	
	@Test
	public void testContinuousPull1()
	{
		FibonacciProcessor fp = new FibonacciProcessor(4);
		Pullable f_pull = fp.getPullableOutput();
		ThreadPullable t_pull = new ThreadPullable(new ContinuousPoller(f_pull));
		t_pull.start();
		BigInteger bi = (BigInteger) t_pull.pull();
		assertNotNull(bi);
		assertEquals(3, bi.intValue());
		t_pull.stop();
	}
	
	@Test
	public void testContinuousPull2()
	{
		FibonacciProcessor fp = new FibonacciProcessor(100);
		Pullable f_pull = fp.getPullableOutput();
		ThreadPullable t_pull = new ThreadPullable(new ContinuousPoller(f_pull));
		t_pull.start();
		BigInteger bi = (BigInteger) t_pull.pull();
		assertNotNull(bi);
		t_pull.stop();
	}
	
	@Test
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
	
	@Test
	public void testContinuousChain1()
	{
		DelayProcessor delay_1 = new DelayProcessor(0, 500);
		Pullable d1_pull = delay_1.getPullableOutput();
		ThreadPullable d1_tpull = new ThreadPullable(new ContinuousPoller(d1_pull));
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
				// processors have worked in parallel
				assertTrue(duration < 800);
			}
			last_time = this_time;
		}
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
		protected Queue<Object[]> compute(Object[] inputs) 
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
				return wrapObject(0);
			}
			return wrapVector(inputs);
		}

		@Override
		public Processor clone() 
		{
			// Don't care
			return null;
		}
		
	}

	public static class FibonacciProcessor extends SingleProcessor
	{
		protected int m_index = 1;
		
		public FibonacciProcessor(int index) 
		{
			super(0, 1);
			m_index = index;
		}

		@Override
		protected Queue<Object[]> compute(Object[] inputs)
		{
			// Perform some long computation
			BigInteger i = fib(m_index);
			return wrapObject(i);
		}

		@Override
		public Processor clone() 
		{
			// Don't care
			return this;
		}

		/**
		 * Computes the n-th Fibonacci number.
		 * The actual result of this computation does not really matter;
		 * here we only use it as a CPU-intensive operation.
		 * @param nth The index of the number
		 * @return The Fibonacci number
		 */
		static BigInteger fib(long nth)
		{
			nth = nth - 1;
			long count = 0;
			BigInteger first = BigInteger.ZERO;
			BigInteger second = BigInteger.ONE;

			BigInteger third = null;
			while(count < nth)
			{
				third = new BigInteger(first.add(second).toString());
				first = new BigInteger(second.toString());
				second = new BigInteger(third.toString());
				count++;
			}
			return third;
		}
	}
	
	/**
	 * Processor that checks the primality of a big integer.
	 * Its goal is not to be efficient, but rather to be CPU-intensive.
	 */
	public static class IsPrime extends SingleProcessor
	{
		public IsPrime()
		{
			super(1, 1);
		}

		@Override
		protected Queue<Object[]> compute(Object[] inputs)
		{
			BigInteger divisor = BigInteger.ONE.add(BigInteger.ONE);
			BigInteger number = (BigInteger) inputs[0];
			boolean prime = true;
			while (divisor.compareTo(number) < 0)
			{
				BigInteger[] result = number.divideAndRemainder(divisor);
				if (result[1].compareTo(BigInteger.ZERO) == 0)
				{
					prime = false;
				}
				divisor.add(BigInteger.ONE);
			}
			return wrapObject(prime);
		}

		@Override
		public Processor clone() 
		{
			// Don't care
			return this;
		}
	}
}
