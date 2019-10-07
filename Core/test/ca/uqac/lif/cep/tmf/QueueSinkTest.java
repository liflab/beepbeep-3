package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Processor.NthEvent;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.SingleProcessorTest;
import ca.uqac.lif.cep.SingleProcessorTestTemplate.IdentityObjectPrinter;
import ca.uqac.lif.cep.SingleProcessorTestTemplate.IdentityObjectReader;
import ca.uqac.lif.cep.tmf.QueueSink.QueueSinkQueryable;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;
import ca.uqac.lif.petitpoucet.graph.UnknownNode;

public class QueueSinkTest
{
	@Test
	public void testPush()
	{
		QueueSink sink = new QueueSink();
		Queue<Object[]> q = sink.getQueue();
		Pushable p = sink.getPushableInput();
		assertTrue(q.isEmpty());
		p.push("foo");
		assertEquals(1, q.size());
		assertEquals("foo", q.peek()[0]);
		p.push("bar");
		assertEquals(2, q.size());
		q.remove();
		assertEquals("bar", q.peek()[0]);
		sink.reset();
		assertEquals(0, q.size());
	}
	
	@Test
	public void testDuplicateState()
	{
		QueueSink sink = new QueueSink();
		Queue<Object[]> q = sink.getQueue();
		Pushable p = sink.getPushableInput();
		assertTrue(q.isEmpty());
		p.push("foo");
		assertEquals(1, q.size());
		assertEquals("foo", q.peek()[0]);
		p.push("bar");
		assertEquals(2, q.size());
		QueueSink sink_dup = sink.duplicate(true);
		assertFalse(sink.m_queue == sink_dup.m_queue);
		Queue<Object[]> q_dup = sink_dup.getQueue();
		assertEquals(2, q_dup.size());
		assertEquals("foo", q_dup.peek()[0]);
		q_dup.remove();
		assertEquals("bar", q_dup.peek()[0]);
		sink_dup.reset();
		assertEquals(0, q_dup.size());
	}
	
	@Test
	public void testDuplicateNoState()
	{
		QueueSink sink = new QueueSink();
		Queue<Object[]> q = sink.getQueue();
		Pushable p = sink.getPushableInput();
		assertTrue(q.isEmpty());
		p.push("foo");
		assertEquals(1, q.size());
		assertEquals("foo", q.peek()[0]);
		p.push("bar");
		assertEquals(2, q.size());
		QueueSink sink_dup = sink.duplicate(false);
		assertFalse(sink.m_queue == sink_dup.m_queue);
		Queue<Object[]> q_dup = sink_dup.getQueue();
		assertEquals(0, q_dup.size());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		QueueSink qs = new QueueSink(2);
		Pushable p1 = qs.getPushableInput(0);
		Pushable p2 = qs.getPushableInput(1);
		p1.push("foo");
		p2.push("bar");
		p1.push("baz");
		p2.push("biz");
		Map<String,Object> printed = (Map<String,Object>) iop.print(qs);
		List<List<Object>> queue = (List<List<Object>>) printed.get(SingleProcessor.s_contentsKey);
		assertEquals(2, queue.size());
		List<Object> front = queue.get(0);
		assertEquals("foo", front.get(0));
		assertEquals("bar", front.get(1));
		front = queue.get(1);
		assertEquals("baz", front.get(0));
		assertEquals("biz", front.get(1));
	}
	
	@Test
	public void testRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		List<List<Object>> p_queue = new ArrayList<List<Object>>(2);
		p_queue.add(QueueSourceTest.createFront("foo", "bar"));
		p_queue.add(QueueSourceTest.createFront("biz", "baz"));
		Map<String,Object> printed = SingleProcessorTest.getPrintedMap(2, 0, new QueueSinkQueryable("fooproc", 2, 0), p_queue);
		QueueSink qs = (QueueSink) new QueueSink(0).read(ior, printed);
		assertNotNull(qs);
		Queue<Object[]> queue = qs.getQueue();
		assertEquals(2, queue.size());
		Object[] front = queue.peek();
		assertEquals("foo", front[0]);
		assertEquals("bar", front[1]);		
	}
	
	/**
	 * Checks that an exception is thrown if one of the fronts' size is not
	 * equal to the processor's input arity
	 * @throws ReadException The expected exception
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid1() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		List<List<Object>> p_queue = new ArrayList<List<Object>>(2);
		p_queue.add(QueueSourceTest.createFront("foo", "bar"));
		p_queue.add(QueueSourceTest.createFront("biz"));
		Map<String,Object> printed = SingleProcessorTest.getPrintedMap(2, 0, new QueueSinkQueryable("fooproc", 2, 0), p_queue);
		new QueueSink(0).read(ior, printed);
	}
	
	/**
	 * Checks that an exception is thrown if the serialized contents of the
	 * processor has the wrong type
	 * @throws ReadException The expected exception
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid2() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		List<List<Object>> p_queue = new ArrayList<List<Object>>(2);
		p_queue.add(QueueSourceTest.createFront("foo", "bar"));
		p_queue.add(QueueSourceTest.createFront("biz"));
		Map<String,Object> printed = SingleProcessorTest.getPrintedMap(2, 0, new QueueSinkQueryable("fooproc", 2, 0), 3);
		new QueueSink(0).read(ior, printed);
	}
	
	/**
	 * Checks that an exception is thrown if one of the fronts is not a list
	 * @throws ReadException The expected exception
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid3() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		List<Object> p_queue = new ArrayList<Object>(1);
		p_queue.add("biz");
		Map<String,Object> printed = SingleProcessorTest.getPrintedMap(2, 0, new QueueSinkQueryable("fooproc", 2, 0), p_queue);
		new QueueSink(0).read(ior, printed);
	}
	
	@Test
	public void testQueryableDuplicateState()
	{
		QueueSinkQueryable qsq = new QueueSinkQueryable("fooproc", 2, 0);
		QueueSinkQueryable qsq_dup = qsq.duplicate(true);
		assertFalse(qsq == qsq_dup);
		assertEquals(2, qsq.getInputArity());
		assertEquals(0, qsq.getOutputArity());
	}
	
	@Test
	public void testQueryableDuplicateNoState()
	{
		QueueSinkQueryable qsq = new QueueSinkQueryable("fooproc", 2, 0);
		QueueSinkQueryable qsq_dup = qsq.duplicate(false);
		assertFalse(qsq == qsq_dup);
		assertEquals(2, qsq.getInputArity());
		assertEquals(0, qsq.getOutputArity());
	}
	
	@Test
	public void testQueryablePrintState()
	{
		QueueSinkQueryable qsq = new QueueSinkQueryable("fooproc", 2, 0);
		assertNull(qsq.printState());
	}
	
	@Test
	public void testQueryableReadState() throws ReadException
	{
		QueueSinkQueryable qsq = new QueueSinkQueryable("fooproc", 2, 0).readState("fooproc", 2, 0, null);
		assertNotNull(qsq);
	}
	
	@Test
	public void testQueryableQueryOutput()
	{
		QueueSinkQueryable qsq = new QueueSinkQueryable("fooproc", 2, 0);
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(0), new NthOutput(0));
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = qsq.query(TraceabilityQuery.TaintQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		assertTrue(leaves.get(0) instanceof UnknownNode);
	}
}
