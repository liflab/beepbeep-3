package concurrency;

import static ca.uqac.lif.cep.Connector.connect;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Queue;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SingleProcessor;

public class ThreadGroups
{
	public static void main(String[] args) throws ConnectorException
	{
		Counter cnt = new Counter();
		IsPrimeProcessor ip1 = new IsPrimeProcessor();
		connect(cnt, ip1);
		GroupProcessor group = new GroupProcessor(0,1);
		//PullThreadGroup group = new PullThreadGroup(0, 1);
		group.addProcessor(cnt);
		group.addProcessor(ip1);
		group.associateOutput(0, ip1, 0);
		IsPrimeProcessor ip = new IsPrimeProcessor();
		connect(group, ip);
		Pullable p = ip.getPullableOutput();
		group.start();
		long start_time = System.currentTimeMillis();
		for (int i = 0; i < 100000; i++)
		{
			Object b = p.pull();
			long this_time = System.currentTimeMillis();
			System.out.println(">> " + i + ": " + b + " " + (this_time - start_time));
		}

	}

	/**
	 * Processor that computes the n-th Fibonacci number.
	 */
	public static class FibonacciProcessor extends SingleProcessor
	{
		protected int m_index = 2;

		public FibonacciProcessor()
		{
			super(0, 1);
		}

		public FibonacciProcessor(int index)
		{
			this();
			m_index = index;
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			// Perform some long computation
			BigInteger i = fib(m_index);
			m_index++;
			System.out.println("FIB : " + (m_index - 1) + " DONE");
			outputs.add(wrapObject(i));
			return true;
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
			//System.out.println("FIB : " + nth);
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
	public static class IsPrimeProcessor extends SingleProcessor
	{
		public IsPrimeProcessor()
		{
			super(1, 1);
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			BigInteger divisor = BigInteger.ONE.add(BigInteger.ONE);
			BigInteger number = (BigInteger) inputs[0];
			BigInteger sqrt_number = sqrt(number);
			@SuppressWarnings("unused")
			boolean prime = true;
			//System.out.println("PRIME : " + number);
			while (divisor.compareTo(sqrt_number) <= 0)
			{
				BigInteger result = number.remainder(divisor);
				if (result.compareTo(BigInteger.ZERO) == 0)
				{
					prime = false;
				}
				divisor = divisor.add(BigInteger.ONE);
			}
			System.out.println("PRIME : " + number + " DONE");
			outputs.add(inputs);
			return true;
		}

		@Override
		public Processor clone()
		{
			// Don't care
			return this;
		}
	}

	/**
	 * Computes the square root of a big decimal
	 * @param n
	 * @return
	 */
	public static BigInteger sqrt(BigInteger n)
	{
		int firsttime = 0;

		BigDecimal myNumber = new BigDecimal(n);
		BigDecimal g = new BigDecimal("1");
		BigDecimal my2 = new BigDecimal("2");
		BigDecimal epsilon = new BigDecimal("0.0000000001");

		BigDecimal nByg = myNumber.divide(g, 9, BigDecimal.ROUND_FLOOR);

		//Get the value of n/g
		BigDecimal nBygPlusg = nByg.add(g);

		//Get the value of "n/g + g
		BigDecimal nBygPlusgHalf =  nBygPlusg.divide(my2, 9, BigDecimal.ROUND_FLOOR);

		//Get the value of (n/g + g)/2
		BigDecimal  saveg = nBygPlusgHalf;
		firsttime = 99;

		do
		{
			g = nBygPlusgHalf;
			nByg = myNumber.divide(g, 9, BigDecimal.ROUND_FLOOR);
			nBygPlusg = nByg.add(g);
			nBygPlusgHalf =  nBygPlusg.divide(my2, 9, BigDecimal.ROUND_FLOOR);
			BigDecimal  savegdiff  = saveg.subtract(nBygPlusgHalf);

			if (savegdiff.compareTo(epsilon) == -1 )
			{
				firsttime = 0;
			}
			else
			{
				saveg = nBygPlusgHalf;
			}

		} while (firsttime > 1);
		return saveg.toBigInteger();
	}

	public static class Counter extends SingleProcessor
	{
		BigInteger count = new BigInteger("100000000000");

		public Counter()
		{
			super(0, 1);
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			BigInteger out = count;
			count = count.add(BigInteger.TEN);
			outputs.add(wrapObject(out));
			return true;
		}

		@Override
		public Processor clone() {
			// TODO Auto-generated method stub
			return null;
		}
	}
}
