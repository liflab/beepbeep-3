package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Processor.NthEvent;
import ca.uqac.lif.cep.Processor.ProcessorException;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.ProcessorQueryableTest;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.SingleProcessorTest;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.cep.tmf.QueueSource.NthOfQueue;
import ca.uqac.lif.cep.tmf.QueueSource.QueueSourceQueryable;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.DesignatedObject;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.common.CollectionDesignator.NthElement;
import ca.uqac.lif.petitpoucet.graph.ConcreteObjectNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;
import ca.uqac.lif.petitpoucet.graph.UnknownNode;

public class QueueSourceTest
{
	@Test
	public void testPullLoop()
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(true);
		Pullable p = qs.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals(2, p.next());
		assertTrue(p.hasNext());
		assertEquals(7, p.next());
		assertTrue(p.hasNext());
		assertEquals(1, p.next());
		assertTrue(p.hasNext());
		assertEquals(2, p.next());
		assertEquals(7, p.next());
		assertTrue(p.hasNext());
	}
	
	@Test
	public void testPullNoLoop()
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(false);
		Pullable p = qs.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals(2, p.next());
		assertTrue(p.hasNext());
		assertEquals(7, p.next());
		assertTrue(p.hasNext());
		assertEquals(1, p.next());
		assertFalse(p.hasNext());
	}
	
	@Test(expected = ProcessorException.class)
	public void testPullEmpty()
	{
		QueueSource qs = new QueueSource().loop(false);
		Pullable p = qs.getPullableOutput();
		assertFalse(p.hasNext());
		p.pull();
	}
	
	@Test
	public void testResetLoop()
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(true);
		Pullable p = qs.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals(2, p.next());
		assertTrue(p.hasNext());
		assertEquals(7, p.next());
		qs.reset();
		assertTrue(p.hasNext());
		assertEquals(2, p.next());
		assertTrue(p.hasNext());
		assertEquals(7, p.next());
	}
	
	@Test
	public void testDuplicateState1()
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(true);
		qs.getPullableOutput().pull();
		qs.getPullableOutput().pull();
		QueueSource qs_dup = qs.duplicate(true);
		assertEquals(qs.m_index, qs_dup.m_index);
		assertEquals(qs.m_loop, qs_dup.m_loop);
		assertFalse(qs.m_queue == qs_dup.m_queue);
	}
	
	@Test
	public void testDuplicateNoState1()
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(true);
		qs.getPullableOutput().pull();
		qs.getPullableOutput().pull();
		QueueSource qs_dup = qs.duplicate(false);
		assertEquals(0, qs_dup.m_index);
		assertEquals(qs.m_loop, qs_dup.m_loop);
		assertFalse(qs.m_queue == qs_dup.m_queue);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(true);
		qs.getPullableOutput().pull();
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> map = (Map<String,Object>) ((Map<String,Object>) iop.print(qs)).get(SingleProcessor.s_contentsKey);
		assertEquals(3, map.size());
		assertTrue(map.containsKey(QueueSource.s_indexKey));
		assertTrue(map.containsKey(QueueSource.s_loopKey));
		assertTrue(map.containsKey(QueueSource.s_queueKey));
		assertEquals(1, map.get(QueueSource.s_indexKey));
		assertEquals(true, map.get(QueueSource.s_loopKey));
		List<List<Object>> queue = (List<List<Object>>) map.get(QueueSource.s_queueKey);
		assertEquals(3, queue.size());
		List<Object> front;
		front = queue.get(0);
		assertEquals(2, front.get(0));
		front = queue.get(1);
		assertEquals(7, front.get(0));
		front = queue.get(2);
		assertEquals(1, front.get(0));
	}
	
	@Test
	public void testRead() throws ReadException
	{
		Map<String,Object> contents = new HashMap<String,Object>();
		contents.put(QueueSource.s_loopKey, false);
		contents.put(QueueSource.s_indexKey, 2);
		List<List<Object>> queue = new ArrayList<List<Object>>();
		queue.add(createFront(2));
		queue.add(createFront(7));
		queue.add(createFront(1));
		contents.put(QueueSource.s_queueKey, queue);
		QueueSourceQueryable qsq = new QueueSourceQueryable("procfoo", 0, 1, 3, false);
		Map<String,Object> map = SingleProcessorTest.getPrintedMap(0, 1, qsq, contents);
		IdentityObjectReader ior = new IdentityObjectReader();
		QueueSource qs = (QueueSource) new QueueSource(1).read(ior, map);
		assertEquals(false, qs.m_loop);
		assertEquals(3, qs.m_queue.size());
		assertEquals(2, qs.m_index);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid1() throws ReadException
	{
		Map<String,Object> contents = new HashMap<String,Object>();
		contents.put(QueueSource.s_loopKey, false);
		List<List<Object>> queue = new ArrayList<List<Object>>();
		queue.add(createFront(2));
		queue.add(createFront(7));
		queue.add(createFront(1));
		contents.put(QueueSource.s_queueKey, queue);
		QueueSourceQueryable qsq = new QueueSourceQueryable("procfoo", 0, 1, 3, false);
		Map<String,Object> map = SingleProcessorTest.getPrintedMap(0, 1, qsq, contents);
		IdentityObjectReader ior = new IdentityObjectReader();
		new QueueSource(1).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid2() throws ReadException
	{
		QueueSourceQueryable qsq = new QueueSourceQueryable("procfoo", 0, 1, 3, false);
		Map<String,Object> map = SingleProcessorTest.getPrintedMap(0, 1, qsq, 3);
		IdentityObjectReader ior = new IdentityObjectReader();
		new QueueSource(1).read(ior, map);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testQueryablePrint() throws PrintException
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(false);
		Queryable q = qs.getQueryable();
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> printed = (Map<String,Object>) iop.print(q);
		assertTrue(printed.containsKey(ProcessorQueryable.s_contentsKey));
		Map<String,Object> map = (Map<String,Object>) printed.get(ProcessorQueryable.s_contentsKey);
		assertEquals(false, map.get(QueueSource.s_loopKey));
		assertEquals(3, map.get(QueueSourceQueryable.s_sizeKey));
	}
	
	@Test
	public void testQueryableRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> contents = getQueryableContentsMap(3, true);
		Map<String,Object> map = ProcessorQueryableTest.getPrintedMap("procfoo", 1, 1, contents);
		QueueSourceQueryable qsq = (QueueSourceQueryable) new QueueSourceQueryable("procfoo", 0, 0, 0, false).read(ior, map);
		assertEquals(true, qsq.m_loop);
		assertEquals(3, qsq.m_queueSize);
	}
	
	@Test(expected = ReadException.class)
	public void testQueryableReadInvalid1() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> contents = new HashMap<String,Object>(2);
		contents.put(QueueSourceQueryable.s_sizeKey, 3);
		Map<String,Object> map = ProcessorQueryableTest.getPrintedMap("procfoo", 1, 1, contents);
		new QueueSourceQueryable("procfoo", 0, 0, 0, false).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testQueryableReadInvalid2() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = ProcessorQueryableTest.getPrintedMap("procfoo", 1, 1, 3);
		new QueueSourceQueryable("procfoo", 0, 0, 0, false).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testQueryableReadInvalid3() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		new QueueSourceQueryable("procfoo", 0, 0, 0, false).read(ior, null);
	}
	
	@Test
	public void testProvenanceNoLoop1()
	{
		TraceabilityNode root;
		NthOfQueue noq;
		NthElement ne;
		ConcreteObjectNode con;
		DesignatedObject dob;
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(false);
		Queryable q = qs.getQueryable();
		Tracer factory = new ConcreteTracer();
		root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(1), new NthOutput(0));
		List<TraceabilityNode> list = q.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, list.size());
		con = (ConcreteObjectNode) list.get(0);
		dob = con.getDesignatedObject();
		ne = (NthElement) dob.getDesignator().peek();
		assertEquals(0, ne.getIndex());
		noq = (NthOfQueue) dob.getDesignator().tail().peek();
		assertEquals(1, noq.getIndex());
	}
	
	@Test
	public void testProvenanceNoLoop2()
	{
		TraceabilityNode root;
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(false);
		Queryable q = qs.getQueryable();
		Tracer factory = new ConcreteTracer();
		root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(4), new NthOutput(0));
		List<TraceabilityNode> list = q.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, list.size());
		assertTrue(list.get(0) instanceof UnknownNode);
	}
	
	@Test
	public void testProvenanceLoop1()
	{
		TraceabilityNode root;
		NthOfQueue noq;
		NthElement ne;
		ConcreteObjectNode con;
		DesignatedObject dob;
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(true);
		Queryable q = qs.getQueryable();
		Tracer factory = new ConcreteTracer();
		root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(1), new NthOutput(0));
		List<TraceabilityNode> list = q.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, list.size());
		con = (ConcreteObjectNode) list.get(0);
		dob = con.getDesignatedObject();
		ne = (NthElement) dob.getDesignator().peek();
		assertEquals(0, ne.getIndex());
		noq = (NthOfQueue) dob.getDesignator().tail().peek();
		assertEquals(1, noq.getIndex());
	}
	
	@Test
	public void testProvenanceBinary()
	{
		TraceabilityNode root;
		NthOfQueue noq;
		NthElement ne;
		ConcreteObjectNode con;
		DesignatedObject dob;
		QueueSource qs = new QueueSource(2);
		qs.add(2, 7);
		qs.add(1, 8);
		Queryable q = qs.getQueryable();
		Tracer factory = new ConcreteTracer();
		root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(1), new NthOutput(1));
		List<TraceabilityNode> list = q.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, list.size());
		con = (ConcreteObjectNode) list.get(0);
		dob = con.getDesignatedObject();
		ne = (NthElement) dob.getDesignator().peek();
		assertEquals(1, ne.getIndex());
		noq = (NthOfQueue) dob.getDesignator().tail().peek();
		assertEquals(1, noq.getIndex());
	}
	
	@Test
	public void testProvenanceLoop2()
	{
		TraceabilityNode root;
		NthOfQueue noq;
		NthElement ne;
		ConcreteObjectNode con;
		DesignatedObject dob;
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(true);
		Queryable q = qs.getQueryable();
		Tracer factory = new ConcreteTracer();
		root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(4), new NthOutput(0));
		List<TraceabilityNode> list = q.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, list.size());
		con = (ConcreteObjectNode) list.get(0);
		dob = con.getDesignatedObject();
		ne = (NthElement) dob.getDesignator().peek();
		assertEquals(0, ne.getIndex());
		noq = (NthOfQueue) dob.getDesignator().tail().peek();
		assertEquals(1, noq.getIndex());
	}
	
	@Test
	public void testProvenanceUnknown1()
	{
		TraceabilityNode root;
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(false);
		Queryable q = qs.getQueryable();
		Tracer factory = new ConcreteTracer();
		root = factory.getAndNode();
		List<TraceabilityNode> list = q.query(TraceabilityQuery.ProvenanceQuery.instance, Designator.identity, root, factory);
		assertEquals(1, list.size());
		assertTrue(list.get(0) instanceof UnknownNode);
	}
	
	@Test
	public void testProvenanceUnknown2()
	{
		TraceabilityNode root;
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(false);
		Queryable q = qs.getQueryable();
		Tracer factory = new ConcreteTracer();
		root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(1), new NthInput(0));
		List<TraceabilityNode> list = q.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, list.size());
		assertTrue(list.get(0) instanceof UnknownNode);
	}
	
	@Test
	public void testProvenanceUnknown3()
	{
		TraceabilityNode root;
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(false);
		Queryable q = qs.getQueryable();
		Tracer factory = new ConcreteTracer();
		root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthInput(0), new NthOutput(0));
		List<TraceabilityNode> list = q.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, list.size());
		assertTrue(list.get(0) instanceof UnknownNode);
	}
	
	@Test
	public void testNthOfQueue()
	{
		NthOfQueue ne = new NthOfQueue(3);
		assertFalse(ne.appliesTo(3));
		Queue<Object> q = new ArrayDeque<Object>(0);
		assertTrue(ne.appliesTo(q));
		assertEquals(ne, ne.peek());
		assertNull(ne.tail());
		assertNotNull(ne.toString());
	}
	
	public static List<Object> createFront(Object ... objects)
	{
		List<Object> list = new ArrayList<Object>(objects.length);
		for (Object o : objects)
		{
			list.add(o);
		}
		return list;
	}
	
	protected static Map<String,Object> getQueryableContentsMap(int size, boolean loop)
	{
		Map<String,Object> contents = new HashMap<String,Object>(2);
		contents.put(QueueSourceQueryable.s_sizeKey, size);
		contents.put(QueueSource.s_loopKey, loop);
		return contents;
	}
}
