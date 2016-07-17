package ca.uqac.lif.cep.epl;

import static org.junit.Assert.*;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.BinaryFunction;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pushable;

/**
 * Unit tests for the {@link WindowFunction} processor
 * @author Sylvain Hallé
 */
public class WindowFunctionTest
{
	@Test
	public void test1() throws ConnectorException
	{
		Object value = 0;
		WindowFunction wf = new WindowFunction(new DummyPlus());
		QueueSink sink = new QueueSink(1);
		Connector.connect(wf, sink);
		Queue<Object> queue = sink.getQueue(0);
		Pushable p1 = wf.getPushableInput(0);
		p1.push(2);
		assertTrue(queue.isEmpty());
		p1.push(3);
		assertFalse(queue.isEmpty());
		value = queue.remove();
		assertTrue(value instanceof Integer);
		assertEquals(5, ((Integer) value).intValue());
		p1.push(9);
		assertFalse(queue.isEmpty());
		value = queue.remove();
		assertEquals(12, ((Integer) value).intValue());
	}
	
	public static class DummyPlus extends BinaryFunction<Integer,Integer,Integer> 
	{
		public DummyPlus()
		{
			super(Integer.class, Integer.class, Integer.class);
		}

		@Override
		public Integer evaluate(Integer x, Integer y) 
		{
			return x.intValue() + y.intValue();
		}
	}
}
