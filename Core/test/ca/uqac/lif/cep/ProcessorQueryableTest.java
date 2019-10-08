package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.cep.TestUtilities.TestableSingleProcessor;
import ca.uqac.lif.petitpoucet.DesignatedObject;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.graph.ConcreteObjectNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;
import ca.uqac.lif.petitpoucet.graph.UnknownNode;

public class ProcessorQueryableTest 
{
	@Test
	public void testQueryableUnknownUpstream()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.ProvenanceQuery.instance, new NthInput(0), root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableWrongDirection()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.TaintQuery.instance, new NthOutput(0), root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableWrongInputArity()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.ProvenanceQuery.instance, new NthInput(3), root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableWrongOutputArity()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.ProvenanceQuery.instance, new NthInput(3), root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableUnknownDesignator()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.ProvenanceQuery.instance, Designator.unknown, root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableConnectedUpstream1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_up = new TestableSingleProcessor(1, 1);
		Connector.connect(spw_up, spw);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		assertEquals(spw_up.getQueryable(), pq.getInputConnection(0).getObject());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.ProvenanceQuery.instance, new NthInput(0), root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode leaf = (ConcreteObjectNode) leaves.get(0);
		DesignatedObject dob = leaf.getDesignatedObject();
		NthOutput no = (NthOutput) dob.getDesignator().peek();
		assertEquals(0, no.getIndex());
		assertEquals(spw_up.getQueryable(), dob.getObject());
	}
	
	@Test
	public void testQueryableConnectedUpstream2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_up = new TestableSingleProcessor(1, 1);
		Connector.connect(spw_up, spw);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.ProvenanceQuery.instance, new NthOutput(0), root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableConnectedDownstream1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_dn = new TestableSingleProcessor(1, 1);
		Connector.connect(spw, spw_dn);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		assertEquals(spw_dn.getQueryable(), pq.getOutputConnection(0).getObject());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.TaintQuery.instance, new NthOutput(0), root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode leaf = (ConcreteObjectNode) leaves.get(0);
		DesignatedObject dob = leaf.getDesignatedObject();
		NthInput no = (NthInput) dob.getDesignator().peek();
		assertEquals(0, no.getIndex());
		assertEquals(spw_dn.getQueryable(), dob.getObject());
	}
	
	@Test
	public void testQueryableConnectedDownstream2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_dn = new TestableSingleProcessor(1, 1);
		Connector.connect(spw, spw_dn);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.ProvenanceQuery.instance, new NthInput(0), root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableUpstreamOutOfBounds()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_up = new TestableSingleProcessor(1, 1);
		Connector.connect(spw_up, spw);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.ProvenanceQuery.instance, new NthInput(3), root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableDownstreamOutOfBounds()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_dn = new TestableSingleProcessor(1, 1);
		Connector.connect(spw, spw_dn);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		Tracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = pq.query(TraceabilityQuery.TaintQuery.instance, new NthOutput(3), root, factory);
		assertEquals(1, leaves.size());
		TraceabilityNode leaf = leaves.get(0);
		assertNotNull(leaf);
		assertTrue(leaf instanceof UnknownNode);
	}
	
	@Test
	public void testDuplicateNoState()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		ProcessorQueryable pq_dup = (ProcessorQueryable) pq.duplicate();
		assertFalse(pq == pq_dup);
		assertEquals(pq.getInputArity(), pq_dup.getInputArity());
		assertEquals(pq.getOutputArity(), pq_dup.getOutputArity());
	}
	
	@Test
	public void testDuplicateState()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		ProcessorQueryable pq_dup = (ProcessorQueryable) pq.duplicate(true);
		assertFalse(pq == pq_dup);
		assertEquals(pq.getInputArity(), pq_dup.getInputArity());
		assertEquals(pq.getOutputArity(), pq_dup.getOutputArity());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 1);
		ProcessorQueryable q = (ProcessorQueryable) spw.getQueryable();
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> printed = (Map<String,Object>) iop.print(q);
		assertEquals(2, printed.size());
		assertTrue(printed.containsKey(ProcessorQueryable.s_arityKey));
		List<Integer> arity_list = (List<Integer>) printed.get(ProcessorQueryable.s_arityKey);
		assertEquals(2, arity_list.size());
		assertEquals(2, (int) arity_list.get(0));
		assertEquals(1, (int) arity_list.get(1));
		assertTrue(printed.containsKey(ProcessorQueryable.s_referenceKey));
		assertEquals(spw.toString(), printed.get(ProcessorQueryable.s_referenceKey));
	}
	
	@Test
	public void testRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = getPrintedMap("procfoo", 2, 3, null);
		ProcessorQueryable pq = (ProcessorQueryable) new ProcessorQueryable("procfoo", 1, 1).read(ior, map);
		assertEquals(2, pq.m_inputConnections.length);
		assertEquals(3, pq.m_outputConnections.length);
		assertEquals("procfoo", pq.m_reference);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid1() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = new HashMap<String,Object>();
		new ProcessorQueryable("procfoo", 1, 1).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid2() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		new ProcessorQueryable("procfoo", 1, 1).read(ior, 3);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid4() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = getPrintedMap("procfoo", 2, 3, null);
		map.remove(ProcessorQueryable.s_arityKey);
		new ProcessorQueryable("procfoo", 1, 1).read(ior, map);
	}
	
	@SuppressWarnings("unchecked")
	@Test(expected = ReadException.class)
	public void testReadInvalid5() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = getPrintedMap("procfoo", 2, 3, null);
		((List<Integer>) map.get(ProcessorQueryable.s_arityKey)).remove(0);
		new ProcessorQueryable("procfoo", 1, 1).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid6() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = getPrintedMap("procfoo", 2, 3, null);
		map.put(ProcessorQueryable.s_arityKey, 3);
		new ProcessorQueryable("procfoo", 1, 1).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid3() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = getPrintedMap("procfoo", 2, 3, null);
		map.remove(ProcessorQueryable.s_referenceKey);
		new ProcessorQueryable("procfoo", 1, 1).read(ior, map);
	}
	
	public static Map<String,Object> getPrintedMap(String reference, int in_arity, int out_arity, Object contents)
	{
		Map<String,Object> map = new HashMap<String,Object>();
		List<Integer> list = new ArrayList<Integer>(2);
		list.add(in_arity);
		list.add(out_arity);
		map.put(ProcessorQueryable.s_arityKey, list);
		map.put(ProcessorQueryable.s_referenceKey, reference);
		if (contents != null)
		{
			map.put(ProcessorQueryable.s_contentsKey, contents);
		}
		return map;
	}
}
