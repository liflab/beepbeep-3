package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import java.util.ArrayDeque;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.clone.IdentityPrintHandler;
import ca.uqac.lif.azrael.clone.IdentityReadHandler;
import ca.uqac.lif.azrael.clone.ReadableReadHandler;
import ca.uqac.lif.cep.tmf.QueueSource;

public class SingleProcessorTestTemplate 
{
	/**
	 * Checks the declared input and output arity
	 * @param p The processor to test on
	 * @param in_arity The expected input arity
	 * @param out_arity The expected output arity
	 */
	public static void testArity(Processor p, int in_arity, int out_arity)
	{
		assertEquals(in_arity, p.getInputArity());
		assertEquals(out_arity, p.getOutputArity());
	}
	
	/**
	 * Tests the behaviour of the processor when being duplicated.
	 * Conditions to be followed:
	 * <ol>
	 * <li>Duplicating results in a non-null object of the same class as the
	 * original, and the same input/output arity</li>
	 * <li>The context contents are preserved in the duplicate</li>
	 * <li>The context contents are independent from the original's context
	 * object</li>
	 * </ol>
	 * @param p The processor to test on
	 */
	public static void testDuplicate1(Processor p)
	{
		p.setContext("foo", "bar");
		Processor dup = p.duplicate();
		assertNotNull(dup);
		assertEquals(p.getClass(), dup.getClass());
		assertEquals(p.getInputArity(), dup.getInputArity());
		assertEquals(p.getOutputArity(), dup.getOutputArity());
		assertEquals("bar", dup.getContext("foo"));
		p.setContext("baz", "123");
		assertNull(dup.getContext("baz"));
	}
	
	/**
	 * Checks that each input pushable given by the processor is not null, and
	 * that asking twice for the same pushable returns the same object.
	 * @param p The processor to test on
	 */
	public static void testMultiplePushable1(Processor p)
	{
		for (int i = 0; i < p.getInputArity(); i++)
		{
			Pushable push = p.getPushableInput(i);
			assertNotNull(push);
			Pushable push2 = p.getPushableInput(i);
			assertEquals(push, push2);
		}
	}
	
	/**
	 * Checks that each output pullable given by the processor is not null, and
	 * that asking twice for the same pullable returns the same object.
	 * @param p The processor to test on
	 */
	public static void testMultiplePullable1(Processor p)
	{
		for (int i = 0; i < p.getOutputArity(); i++)
		{
			Pullable pull = p.getPullableOutput(i);
			assertNotNull(pull);
			Pullable pull2 = p.getPullableOutput(i);
			assertEquals(pull, pull2);
		}
	}
	
	@Test
	public void dummyTest()
	{
		assertTrue(true);
	}
	
	/**
	 * A processor that provides additional public methods to expose the
	 * internal fields of the {@link SingleProcessor} class. This is used in
	 * unit tests to control the behaviour of the class under various
	 * circumstances.
	 */
	public static class SingleProcessorWrapper extends SingleProcessor
	{
		protected boolean m_computeReturn = true;

		protected Queue<Object[]> m_fronts;

		protected int m_callsToEnd = 0;
		
		protected int m_callsToStart = 0;
		
		protected int m_callsToStop = 0;
		
		protected int m_callsToReset = 0;

		protected int m_stutterAmount = 1;
		
		protected Class<?> m_inputType = Object.class;
		
		protected Class<?> m_outputType = Object.class;
		
		protected Object m_state = null;

		public SingleProcessorWrapper(int in_arity, int out_arity)
		{
			super(in_arity, out_arity);
			m_fronts = new ArrayDeque<Object[]>();
			m_queryable = new ProcessorQueryable(toString(), in_arity, out_arity);
		}
		
		public void setState(Object o)
		{
			m_state = o;
		}
		
		public Object getState()
		{
			return m_state;
		}
		
		public void setInputType(Class<?> c)
		{
			m_inputType = c;
		}
		
		public void setOutputType(Class<?> c)
		{
			m_outputType = c;
		}
		
		@Override
		public Class<?> getInputType(int index)
		{
			return m_inputType;
		}
		
		@Override
		public Class<?> getOutputType(int index)
		{
			return m_outputType;
		}
		
		public Pullable getInputPullable(int index)
		{
			return m_inputPullables[index];
		}
		
		public Pushable getOutputPushable(int index)
		{
			return m_outputPushables[index];
		}

		public void setStutterAmount(int n)
		{
			m_stutterAmount = n;
		}

		public int getCallsToEnd()
		{
			return m_callsToEnd;
		}
		
		public int getCallsToReset()
		{
			return m_callsToReset;
		}

		public Context getContextMap()
		{
			return m_context;
		}

		public Queue<Object> getInputQueue(int index)
		{
			return m_inputQueues[index];
		}

		public Queue<Object> getOutputQueue(int index)
		{
			return m_outputQueues[index];
		}

		public Queue<Object[]> getFronts()
		{
			return m_fronts;
		}
		
		@Override
		public void start()
		{
			m_callsToStart++;
		}
		
		@Override
		public void stop()
		{
			m_callsToStop++;
		}
		
		@Override
		public void reset()
		{
			m_callsToReset++;
			super.reset();
		}

		@Override
		public SingleProcessorWrapper duplicate(boolean with_state) 
		{
			SingleProcessorWrapper spw = new SingleProcessorWrapper(m_inputQueues.length, m_outputQueues.length);
			return (SingleProcessorWrapper) copyInto(spw, with_state);
		}

		@Override
		public boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			for (int i = 0; i < m_stutterAmount; i++)
			{
				outputs.add(inputs);
			}
			m_fronts.add(inputs);
			return m_computeReturn;
		}

		@Override
		public void onEnd(Queue<Object[]> outputs)
		{
			m_callsToEnd++;
			// We create a special output front that can be detected
			Object[] out_front = new Object[getOutputArity()];
			for (int i = 0; i < out_front.length; i++)
			{
				out_front[i] = 999;
			}
			outputs.add(out_front);
		}

		@Override
		protected SingleProcessor readState(Object state, int in_arity, int out_arity) 
		{
			SingleProcessorWrapper spw = new SingleProcessorWrapper(in_arity, out_arity);
			spw.m_state = state;
			return spw;
		}

		@Override
		protected Object printState() 
		{
			return m_state;
		}
		
		public int getCallsToStart()
		{
			return m_callsToStart;
		}
		
		public int getCallsToStop()
		{
			return m_callsToStop;
		}
	}

	/**
	 * A configurable {@link QueueSource} with additional methods to expose
	 * its internal state. This is used in
	 * unit tests to control the behaviour of the class under various
	 * circumstances.
	 */
	public static class StutteringQueueSource extends QueueSource
	{
		protected int m_stutterAmount = 1;

		protected int m_computeCount = 0;

		protected void setStutterAmount(int n)
		{
			m_stutterAmount = n;
		}

		protected int getComputeCount()
		{
			return m_computeCount;
		}

		@Override
		public boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			m_computeCount++;
			if (m_stutterAmount < 0)
			{
				if (m_computeCount % (-m_stutterAmount) == 0)
				{
					return super.compute(inputs, outputs);
				}
			}
			else
			{
				for (int i = 0; i < m_stutterAmount; i++)
				{
					if (!super.compute(inputs, outputs))
					{
						return false;
					}
				}
			}
			return true;
		}
	}
	
	public static class IdentityObjectPrinter extends ObjectPrinter<Object>
	{
		public IdentityObjectPrinter()
		{
			super();
			addHandler(new IdentityPrintHandler());
		}
		
		@Override
		public Object wrap(Object o, Object t) throws PrintException 
		{
			return t;
		}
	}
	
	public static class IdentityObjectReader extends ObjectReader<Object>
	{
		public IdentityObjectReader()
		{
			super();
			addHandler(new ReadableReadHandler(this));
			addHandler(new IdentityReadHandler());
		}
		
		public Object read(Object o, Readable reference) throws ReadException
		{
			return reference.read(this, o);
		}

		@Override
		protected Class<?> unwrapType(Object t) throws ReadException
		{
			return t.getClass();
		}

		@Override
		protected Object unwrapContents(Object t) throws ReadException 
		{
			return t;
		}

		@Override
		protected boolean isWrapped(Object t) 
		{
			return false;
		}
	}
	
	public static class QueueSourceWrapper extends QueueSource
	{
		protected int m_callsToCompute = 0;
		
		protected int m_callsToPush = 0;
		
		@Override
		public void push()
		{
			m_callsToPush++;
			super.push();
		}
		
		@Override
		public boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			m_callsToCompute++;
			return super.compute(inputs, outputs);
		}
	}
}
