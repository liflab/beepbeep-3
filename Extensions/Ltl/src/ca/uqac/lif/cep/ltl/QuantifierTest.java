package ca.uqac.lif.cep.ltl;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Unit tests for quantifiers
 * @author Sylvain Hallé
 */
public class QuantifierTest 
{
	@Test
	public void testForAll1() throws ConnectorException
	{
		ForAll fa = new ForAll(new IsEvenProcessor(), new DummyCollectionFunction(), "x", new DummyDomainFunction());
		QueueSink sink = new QueueSink(1);
		Connector.connect(fa, sink);
		Pushable in = fa.getPushableInput(0);
		Queue<Object> queue = sink.getQueue(0);
		in.push(0);
		assertFalse(queue.isEmpty());
		Object output = queue.remove();
		assertNotNull(output);
		assertTrue(output instanceof Troolean.Value);
		assertEquals(Troolean.Value.FALSE, (Troolean.Value) output);
	}

	@SuppressWarnings("rawtypes")
	public static class DummyCollectionFunction extends UnaryFunction<Object,Set>
	{
		public DummyCollectionFunction()
		{
			super(Object.class, Set.class);
		}

		@Override
		public Set<Integer> getValue(Object x) 
		{
			HashSet<Integer> out = new HashSet<Integer>();
			out.add(1);
			out.add(2);
			out.add(3);
			return out;
		}
	}
	
	public static class DummyDomainFunction extends UnaryFunction<Integer,Integer>
	{
		public DummyDomainFunction()
		{
			super(Integer.class, Integer.class);
		}

		@Override
		public Integer getValue(Integer x) 
		{
			return x;
		}
	}
	
	public static class DummyBooleanFunction extends UnaryFunction<Integer,Boolean>
	{
		public DummyBooleanFunction()
		{
			super(Integer.class, Boolean.class);
		}

		@Override
		public Boolean getValue(Integer x) 
		{
			return x.intValue() % 2 == 0;
		}
	}
	
	public static class IsEvenProcessor extends FunctionProcessor
	{
		public IsEvenProcessor()
		{
			super(new DummyBooleanFunction());
		}
	}

}
