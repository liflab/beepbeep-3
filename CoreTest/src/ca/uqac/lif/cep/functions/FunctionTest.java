package ca.uqac.lif.cep.functions;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Palette;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.functions.ArgumentPlaceholder;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.tmf.QueueSink;

/**
 * Unit tests for {@link Function}, {@link UnaryFunction}, {@link BinaryFunction}
 * and {@link CumulativeFunction}.
 * @author Sylvain Hallé
 */
public class FunctionTest extends BeepBeepUnitTest 
{
	@Test
	public void testAdditionOnce() throws ConnectorException
	{
		DummyUnaryFunction duf = new DummyUnaryFunction();
		Integer i = duf.getValue(0);
		assertNotNull(i);
		assertEquals(0, i.intValue());
	}

	@Test
	public void testAddition() throws ConnectorException
	{
		DummyAdditionFunction add = new DummyAdditionFunction();
		Integer i = add.getValue(2, 3);
		assertNotNull(i);
		assertEquals(5, i.intValue());
		add.reset();
		i = add.getValue(2, 3);
		assertNotNull(i);
		assertEquals(5, i.intValue());
	}
	
	@Test
	public void testAdditionPlaceholder() throws ConnectorException
	{
		DummyAdditionFunction add = new DummyAdditionFunction();
		Object[] arguments = new Object[2];
		arguments[0] = 2;
		arguments[1] = new ArgumentPlaceholder("x");
		Context context = new Context();
		context.put("x", 3);
		Object[] result = add.evaluate(arguments, context);
		assertEquals(1, result.length);
		assertNotNull(result[0]);
		assertEquals(5, result[0]);
	}

	@Test
	public void testUnaryAsProcessor() throws ConnectorException
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
	public void testUnaryAsProcessorPlaceholder() throws ConnectorException
	{
		FunctionProcessor fp = new FunctionProcessor(new DummyUnaryFunction());
		Pushable in = fp.getPushableInput(0);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fp,  sink);
		ArgumentPlaceholder ap = new ArgumentPlaceholder("x");
		for (int j = 0; j < 2; j++)
		{
			for (int i = 1; i <= 5; i++)
			{
				fp.setContext("x", i);
				if (i % 2 == 0)
				{
					in.push(ap);
				}
				else
				{
					in.push(i);
				}
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
	public void testAdditionAsProcessor() throws ConnectorException
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
	public void testAdditionAsCumulativeProcessor() throws ConnectorException
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
	public void testAdditionNullAsCumulativeProcessor() throws ConnectorException
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
	public void testAdditionCumulative() throws ConnectorException
	{
		CumulativeFunction<Integer> cf = new CumulativeFunction<Integer>(new DummyAdditionFunction());
		Integer i;
		for (int c = 1; c <= 10; c++)
		{
			i = cf.getValue(1);
			assertEquals(c, i.intValue());
		}
	}

	@Test
	public void testAdditionCumulativeNull() throws ConnectorException
	{
		CumulativeFunction<Integer> cf = new CumulativeFunction<Integer>(new DummyAdditionFunctionNull());
		Integer i;
		for (int c = 1; c <= 10; c++)
		{
			i = cf.getValue(1);
			assertEquals(c, i.intValue());
		}
	}
	
	@Test
	public void testGrammar() throws ConnectorException
	{
		Interpreter interp = new Interpreter();
		interp.extendGrammar(DummyGrammarExtension.class);
	}

	public static class DummyUnaryFunction extends UnaryFunction<Integer,Integer>
	{
		public DummyUnaryFunction()
		{
			super(Integer.class, Integer.class);
		}
		
		@Override
		public Integer getValue(Integer x) 
		{
			return x;
		}
	}

	public static class DummyAdditionFunction extends BinaryFunction<Integer,Integer,Integer>
	{
		public DummyAdditionFunction()
		{
			super(Integer.class, Integer.class, Integer.class);
		}
		
		@Override
		public Integer getValue(Integer x, Integer y) 
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
		public DummyAdditionFunctionNull()
		{
			super(Integer.class, Integer.class, Integer.class);
		}
		
		@Override
		public Integer getValue(Integer x, Integer y) 
		{
			return x.intValue() + y.intValue();
		}
	}
	
	public static class DummyGrammarExtension extends Palette
	{
		public DummyGrammarExtension()
		{
			super(DummyGrammarExtension.class, "");
		}		
	}
}
