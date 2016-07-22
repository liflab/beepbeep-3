package ca.uqac.lif.cep.ltl;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.epl.QueueSource;
import ca.uqac.lif.cep.functions.ArgumentPlaceholder;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.functions.TracePlaceholder;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.numbers.IsGreaterThan;
import ca.uqac.lif.cep.numbers.IsLessThan;

/**
 * Unit tests for quantifiers
 * @author Sylvain Hallé
 */
public class QuantifierTest 
{
	@Test
	public void testForAllPush1() throws ConnectorException
	{
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new TracePlaceholder(0));
		tree.setChild(1, new ArgumentPlaceholder("x"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		ForAll fa = new ForAll("x", new DummyCollectionFunction(1, 2, 3), gt);
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
	
	@Test
	public void testForAllPull1() throws ConnectorException
	{
		QueueSource source = new QueueSource(0, 1);
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new TracePlaceholder(0));
		tree.setChild(1, new ArgumentPlaceholder("x"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		ForAll fa = new ForAll("x", new DummyCollectionFunction(1, 2, 3), gt);
		Connector.connect(source, fa);
		Pullable out = fa.getPullableOutput(0);
		Object output = out.pullHard();
		assertNotNull(output);
		assertTrue(output instanceof Troolean.Value);
		assertEquals(Troolean.Value.FALSE, (Troolean.Value) output);
	}
	
	@Test
	public void testForAll2() throws ConnectorException
	{
		FunctionTree tree = new FunctionTree(IsLessThan.instance); 
		tree.setChild(0, new TracePlaceholder(0));
		tree.setChild(1, new ArgumentPlaceholder("x"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		ForAll fa = new ForAll("x", new DummyCollectionFunction(1, 2, 3), gt);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fa, sink);
		Pushable in = fa.getPushableInput(0);
		Queue<Object> queue = sink.getQueue(0);
		in.push(0);
		assertFalse(queue.isEmpty());
		Object output = queue.remove();
		assertNotNull(output);
		assertTrue(output instanceof Troolean.Value);
		assertEquals(Troolean.Value.TRUE, (Troolean.Value) output);
		in.push(10);
		assertFalse(queue.isEmpty());
		output = queue.remove();
		assertEquals(Troolean.Value.FALSE, (Troolean.Value) output);
	}
	
	@Test
	public void testForAll3() throws ConnectorException
	{
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new ArgumentPlaceholder("x"));
		tree.setChild(1, new ArgumentPlaceholder("y"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		ForAll fa = new ForAll("x", new DummyCollectionFunction(1, 2, 3), gt);
		Exists fa2 = new Exists("y", new DummyCollectionFunction(1, 2, 3), fa);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fa2, sink);
		Pushable in = fa2.getPushableInput(0);
		Queue<Object> queue = sink.getQueue(0);
		in.push(10);
		assertFalse(queue.isEmpty());
		Object output = queue.remove();
		assertNotNull(output);
		assertTrue(output instanceof Troolean.Value);
		assertEquals(Troolean.Value.FALSE, (Troolean.Value) output);
	}
	
	@Test
	public void testForAllPull3() throws ConnectorException
	{
		QueueSource source = new QueueSource(0, 1);
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new ArgumentPlaceholder("x"));
		tree.setChild(1, new ArgumentPlaceholder("y"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		ForAll fa = new ForAll("x", new DummyCollectionFunction(1, 2, 3), gt);
		Exists fa2 = new Exists("y", new DummyCollectionFunction(1, 2, 3), fa);
		Connector.connect(source, fa2);
		Pullable out = fa2.getPullableOutput(0);
		Object output = out.pull();
		assertNotNull(output);
		assertTrue(output instanceof Troolean.Value);
		assertEquals(Troolean.Value.FALSE, (Troolean.Value) output);
	}
	
	@Test
	public void testForAll4() throws ConnectorException
	{
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new ArgumentPlaceholder("y"));
		tree.setChild(1, new ArgumentPlaceholder("x"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		ForAll fa = new ForAll("x", new DummyCollectionFunction(1, 2, 3), gt);
		Exists fa2 = new Exists("y", new DummyCollectionFunction(2, 3, 4), fa);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fa2, sink);
		Pushable in = fa2.getPushableInput(0);
		Queue<Object> queue = sink.getQueue(0);
		in.push(10);
		assertFalse(queue.isEmpty());
		Object output = queue.remove();
		assertNotNull(output);
		assertTrue(output instanceof Troolean.Value);
		assertEquals(Troolean.Value.TRUE, (Troolean.Value) output);
	}
	
	@Test
	public void testExists1() throws ConnectorException
	{
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new TracePlaceholder(0));
		tree.setChild(1, new ArgumentPlaceholder("x"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		Exists fa = new Exists("x", new DummyCollectionFunction(1, 2, 3), gt);
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

	@Test
	public void testExists2() throws ConnectorException
	{
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new TracePlaceholder(0));
		tree.setChild(1, new ArgumentPlaceholder("x"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		Exists fa = new Exists("x", new DummyCollectionFunction(1, 2, 3), gt);
		QueueSink sink = new QueueSink(1);
		Connector.connect(fa, sink);
		Pushable in = fa.getPushableInput(0);
		Queue<Object> queue = sink.getQueue(0);
		in.push(2);
		assertFalse(queue.isEmpty());
		Object output = queue.remove();
		assertNotNull(output);
		assertTrue(output instanceof Troolean.Value);
		assertEquals(Troolean.Value.TRUE, (Troolean.Value) output);
	}

	@SuppressWarnings("rawtypes")
	public static class DummyCollectionFunction extends UnaryFunction<Object,Set>
	{
		Set<Integer> m_values = new HashSet<Integer>();
		
		public DummyCollectionFunction(Integer ... values)
		{
			super(Object.class, Set.class);
			for (Integer v : values)
			{
				m_values.add(v);
			}
		}

		@Override
		public Set<Integer> getValue(Object x) 
		{
			return m_values;
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
