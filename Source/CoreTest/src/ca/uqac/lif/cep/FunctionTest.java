package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.epl.QueueSink;

/**
 * Unit tests for {@link Function}, {@link UnaryFunction}, {@link BinaryFunction}
 * and {@link CumulativeFunction}.
 * @author Sylvain Hallé
 */
public class FunctionTest 
{
	@Test
	public void testAdditionOnce()
	{
		DummyUnaryFunction duf = new DummyUnaryFunction();
		Integer i = duf.evaluate(0);
		assertNotNull(i);
		assertEquals(0, i.intValue());
	}

	@Test
	public void testAddition()
	{
		DummyAdditionFunction add = new DummyAdditionFunction();
		Integer i = add.evaluate(2, 3);
		assertNotNull(i);
		assertEquals(5, i.intValue());
		add.reset();
		i = add.evaluate(2, 3);
		assertNotNull(i);
		assertEquals(5, i.intValue());
	}

	@Test
	public void testUnaryAsProcessor()
	{
		FunctionProcessor fp = new FunctionProcessor(new DummyUnaryFunction());
		Pushable in = fp.getPushableInput(0);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fp,  sink);
		for (int j = 0; j < 2; j++)
		{
			for (int i = 1; i <= 5; i++)
			{
				in.push(i);
				Queue<Object> out = sink.getQueue(0);
				assertFalse(out.isEmpty());
				Object o = out.remove();
				assertNotNull(o);
				assertTrue("Expected Integer, got " + out.getClass().getName(), o instanceof Integer);
				assertEquals(i, ((Integer) o).intValue());
			}
			fp.reset();
		}
	}

	@Test
	public void testAdditionAsProcessor()
	{
		FunctionProcessor fp = new FunctionProcessor(new DummyAdditionFunction());
		Pushable in1 = fp.getPushableInput(0);
		Pushable in2 = fp.getPushableInput(1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fp,  sink);
		for (int j = 0; j < 2; j++)
		{
			for (int i = 1; i <= 5; i++)
			{
				in1.push(i);
				in2.push(i + 1);
				Queue<Object> out = sink.getQueue(0);
				assertFalse(out.isEmpty());
				Object o = out.remove();
				assertNotNull(o);
				assertTrue("Expected Integer, got " + out.getClass().getName(), o instanceof Integer);
				assertEquals(2 * i + 1, ((Integer) o).intValue());
			}
			fp.reset();
		}
	}

	@Test
	public void testAdditionAsCumulativeProcessor()
	{
		FunctionProcessor fp = new FunctionProcessor(new CumulativeFunction<Integer>(new DummyAdditionFunction()));
		Pushable in = fp.getPushableInput(0);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fp,  sink);
		for (int j = 0; j < 2; j++)
		{
			for (int i = 1; i <= 5; i++)
			{
				in.push(i);
				Queue<Object> out = sink.getQueue(0);
				assertFalse(out.isEmpty());
				Object o = out.remove();
				assertNotNull(o);
				assertTrue("Expected Integer, got " + out.getClass().getName(), o instanceof Integer);
				assertEquals(i * (i+1) / 2, ((Integer) o).intValue());
			}
			fp.reset();
		}
	}

	@Test
	public void testAdditionNullAsCumulativeProcessor()
	{
		FunctionProcessor fp = new FunctionProcessor(new CumulativeFunction<Integer>(new DummyAdditionFunctionNull()));
		Pushable in = fp.getPushableInput(0);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fp,  sink);
		for (int j = 0; j < 2; j++)
		{
			for (int i = 1; i <= 5; i++)
			{
				in.push(i);
				Queue<Object> out = sink.getQueue(0);
				assertFalse(out.isEmpty());
				Object o = out.remove();
				assertNotNull(o);
				assertTrue("Expected Integer, got " + out.getClass().getName(), o instanceof Integer);
				assertEquals(i * (i+1) / 2, ((Integer) o).intValue());
			}
			fp.reset();
		}
	}

	@Test
	public void testAdditionCumulative()
	{
		CumulativeFunction<Integer> cf = new CumulativeFunction<Integer>(new DummyAdditionFunction());
		Integer i;
		for (int c = 1; c <= 10; c++)
		{
			i = cf.evaluate(1);
			assertEquals(c, i.intValue());
		}
	}

	@Test
	public void testAdditionCumulativeNull()
	{
		CumulativeFunction<Integer> cf = new CumulativeFunction<Integer>(new DummyAdditionFunctionNull());
		Integer i;
		for (int c = 1; c <= 10; c++)
		{
			i = cf.evaluate(1);
			assertEquals(c, i.intValue());
		}
	}

	public static class DummyUnaryFunction extends UnaryFunction<Integer,Integer>
	{
		@Override
		public Integer evaluate(Integer x) 
		{
			return x;
		}
	}

	public static class DummyAdditionFunction extends BinaryFunction<Integer,Integer,Integer>
	{
		@Override
		public Integer evaluate(Integer x, Integer y) 
		{
			return x.intValue() + y.intValue();
		}

		@Override
		public Integer getStartValue()
		{
			return 0;
		}
	}

	public static class DummyAdditionFunctionNull extends BinaryFunction<Integer,Integer,Integer>
	{
		@Override
		public Integer evaluate(Integer x, Integer y) 
		{
			return x.intValue() + y.intValue();
		}
	}

}
