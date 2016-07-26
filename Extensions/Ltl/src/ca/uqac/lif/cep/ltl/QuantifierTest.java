package ca.uqac.lif.cep.ltl;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Passthrough;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.SmartFork;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.epl.QueueSource;
import ca.uqac.lif.cep.functions.ArgumentPlaceholder;
import ca.uqac.lif.cep.functions.Equals;
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
		Every fa = new Every("x", new DummyCollectionFunction(1, 2, 3), gt);
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
		Every fa = new Every("x", new DummyCollectionFunction(1, 2, 3), gt);
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
		Every fa = new Every("x", new DummyCollectionFunction(1, 2, 3), gt);
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
		assertEquals(Troolean.Value.TRUE, (Troolean.Value) output);
	}
	
	@Test
	public void testForAll3() throws ConnectorException
	{
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new ArgumentPlaceholder("x"));
		tree.setChild(1, new ArgumentPlaceholder("y"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		Every fa = new Every("x", new DummyCollectionFunction(1, 2, 3), gt);
		Some fa2 = new Some("y", new DummyCollectionFunction(1, 2, 3), fa);
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
		Every fa = new Every("x", new DummyCollectionFunction(1, 2, 3), gt);
		Some fa2 = new Some("y", new DummyCollectionFunction(1, 2, 3), fa);
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
		Every fa = new Every("x", new DummyCollectionFunction(1, 2, 3), gt);
		Some fa2 = new Some("y", new DummyCollectionFunction(2, 3, 4), fa);
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
	public void testForAllPull5() throws ConnectorException
	{
		QueueSource source = new QueueSource(0, 1);
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new ArgumentPlaceholder("y"));
		tree.setChild(1, new ArgumentPlaceholder("x"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		Every fa = new Every("x", new DummyCollectionFunction(2), gt);
		Every fa2 = new Every("y", new DummyCollectionFunction(1), fa);
		Connector.connect(source, fa2);
		Pullable out = fa2.getPullableOutput(0);
		Object output = out.pullHard();
		assertNotNull(output);
		assertTrue(output instanceof Troolean.Value);
		assertEquals(Troolean.Value.FALSE, (Troolean.Value) output);
	}
	
	@Test
	public void testExists1() throws ConnectorException
	{
		FunctionTree tree = new FunctionTree(IsGreaterThan.instance); 
		tree.setChild(0, new TracePlaceholder(0));
		tree.setChild(1, new ArgumentPlaceholder("x"));
		FunctionProcessor gt = new FunctionProcessor(tree);
		Some fa = new Some("x", new DummyCollectionFunction(1, 2, 3), gt);
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
		Some fa = new Some("x", new DummyCollectionFunction(1, 2, 3), gt);
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
	
	@Test
	public void testGroupClone1() throws ConnectorException
	{
		Pullable p;
		Object o;
		TrooleanImplies imp = new TrooleanImplies();
		SmartFork fork = new SmartFork(2);
		FunctionProcessor left = new FunctionProcessor(new FunctionTree(TrooleanCast.instance, new FunctionTree(Equals.instance, new TracePlaceholder(0), new TracePlaceholder(0))));
		FunctionProcessor right = new FunctionProcessor(new FunctionTree(TrooleanCast.instance, new FunctionTree(Equals.instance, new TracePlaceholder(0), new TracePlaceholder(0))));
		Connector.connect(fork, left, 0, 0);
		Connector.connect(fork, right, 1, 0);
		Connector.connect(left, imp, 0, 0);
		Connector.connect(right, imp, 0, 1);
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.addProcessors(imp, fork, left, right);
		gp.associateInput(0, fork, 0);
		gp.associateOutput(0, imp, 0);
		// Check that first group works
		QueueSource source1 = new QueueSource(0, 1);
		Connector.connect(source1, gp);
		p = gp.getPullableOutput(0);
		o = p.pullHard();
		assertEquals(o, Troolean.Value.TRUE);
		// Now clone and re-check
		GroupProcessor gp_clone = gp.clone();
		QueueSource source2 = new QueueSource(0, 1);
		Connector.connect(source2, gp_clone);
		p = gp_clone.getPullableOutput(0);
		o = p.pullHard();
		assertEquals(o, Troolean.Value.TRUE);
	}
	
	@Test
	public void testGroupClone2() throws ConnectorException
	{
		Pullable p;
		Object o;
		TrooleanImplies imp = new TrooleanImplies();
		SmartFork fork = new SmartFork(2);
		FunctionProcessor left = new FunctionProcessor(new FunctionTree(TrooleanCast.instance, new FunctionTree(Equals.instance, new TracePlaceholder(0), new TracePlaceholder(0))));
		FunctionProcessor right = new FunctionProcessor(new FunctionTree(TrooleanCast.instance, new FunctionTree(Equals.instance, new TracePlaceholder(0), new ArgumentPlaceholder("x"))));
		Connector.connect(fork, left, 0, 0);
		Connector.connect(fork, right, 1, 0);
		Connector.connect(left, imp, 0, 0);
		Connector.connect(right, imp, 0, 1);
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.addProcessors(imp, fork, left, right);
		gp.associateInput(0, fork, 0);
		gp.associateOutput(0, imp, 0);
		Every fa = new Every("x", new DummyCollectionFunction(1, 2, 3), gp);
		// Check that first group works
		QueueSource source1 = new QueueSource(0, 1);
		Connector.connect(source1, fa);
		p = fa.getPullableOutput(0);
		o = p.pullHard();
		assertEquals(o, Troolean.Value.FALSE);
		// Now clone and re-check
		Every gp_clone = fa.clone();
		QueueSource source2 = new QueueSource(0, 1);
		Connector.connect(source2, gp_clone);
		p = gp_clone.getPullableOutput(0);
		o = p.pullHard();
		assertEquals(o, Troolean.Value.FALSE);
	}
	
	@Test
	public void testGroupClone3() throws ConnectorException
	{
		Pullable p;
		Object o;
		Passthrough pt = new Passthrough(1);
		FunctionProcessor left = new FunctionProcessor(new FunctionTree(TrooleanCast.instance, new FunctionTree(Equals.instance, new TracePlaceholder(0), new TracePlaceholder(0))));
		Every fa = new Every("x", new DummyCollectionFunction(1, 2, 3), left);
		Connector.connect(pt, fa);
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.addProcessors(pt, fa);
		gp.associateInput(0, pt, 0);
		gp.associateOutput(0, fa, 0);
		// Check that first group works
		QueueSource source1 = new QueueSource(0, 1);
		Connector.connect(source1, fa);
		p = fa.getPullableOutput(0);
		o = p.pullHard();
		assertEquals(o, Troolean.Value.TRUE);
		// Now clone and re-check
		Every gp_clone = fa.clone();
		QueueSource source2 = new QueueSource(0, 1);
		Connector.connect(source2, gp_clone);
		p = gp_clone.getPullableOutput(0);
		o = p.pullHard();
		assertEquals(o, Troolean.Value.TRUE);
		o = p.pullHard();
		assertEquals(o, Troolean.Value.TRUE);
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
