package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.SingleProcessorTest;
import ca.uqac.lif.cep.Processor.NthEvent;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.ProcessorQueryableTest;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.cep.tmf.CountDecimate.CountDecimateQueryable;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.DesignatedObject;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.graph.ConcreteObjectNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteTraceabilityNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;
import ca.uqac.lif.petitpoucet.graph.UnknownNode;

public class CountDecimateTest
{
	@Test
	public void testOutput()
	{
		CountDecimate cd = new CountDecimate(3);
		QueueSource qs = new QueueSource().setEvents(3, 1, 4, 1, 5, 9, 2, 6, 5).loop(false);
		Connector.connect(qs, cd);
		Pullable p = cd.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals(3, p.pull());
		assertTrue(p.hasNext());
		assertEquals(1, p.pull());
		assertTrue(p.hasNext());
		assertEquals(2, p.pull());
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testReset()
	{
		CountDecimate cd = new CountDecimate(3);
		QueueSource qs = new QueueSource().setEvents(3, 1, 4, 1, 5, 9, 2, 6, 5).loop(false);
		Connector.connect(qs, cd);
		Pullable p = cd.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals(3, p.pull());
		assertTrue(p.hasNext());
		assertEquals(1, p.pull());
		assertTrue(p.hasNext());
		assertEquals(2, p.pull());
		cd.reset();
		assertEquals(0, cd.m_currentCount);
		assertEquals(3, cd.m_interval);
		assertTrue(p.hasNext());
		assertEquals(6, p.pull());
	}
	
	@Test
	public void testDuplicateState()
	{
		CountDecimate cd = new CountDecimate(3);
		QueueSource qs = new QueueSource().setEvents(3, 1, 4, 1, 5, 9, 2, 6, 5).loop(false);
		Connector.connect(qs, cd);
		Pullable p = cd.getPullableOutput();
		p.pull();
		p.pull();
		CountDecimate cd_dup = cd.duplicate(true);
		assertFalse(cd == cd_dup);
		assertEquals(cd.m_currentCount, cd_dup.m_currentCount);
		assertEquals(cd.m_interval, cd_dup.m_interval);
	}
	
	@Test
	public void testDuplicateNoState()
	{
		CountDecimate cd = new CountDecimate(3);
		QueueSource qs = new QueueSource().setEvents(3, 1, 4, 1, 5, 9, 2, 6, 5).loop(false);
		Connector.connect(qs, cd);
		Pullable p = cd.getPullableOutput();
		p.pull();
		p.pull();
		CountDecimate cd_dup = cd.duplicate(false);
		assertFalse(cd == cd_dup);
		assertEquals(0, cd_dup.m_currentCount);
		assertEquals(cd.m_interval, cd_dup.m_interval);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		CountDecimate cd = new CountDecimate(3);
		cd.m_currentCount = 2;
		Map<String,Object> printed = (Map<String,Object>) iop.print(cd);
		List<Integer> list = (List<Integer>) printed.get(SingleProcessor.s_contentsKey);
		assertEquals(2, list.size());
		assertEquals(3, (int) list.get(0));
		assertEquals(2, (int) list.get(1));
	}
	
	@Test
	public void testRead() throws ReadException
	{
		List<Integer> list = new ArrayList<Integer>(2);
		list.add(3);
		list.add(2);
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = SingleProcessorTest.getPrintedMap(1, 1, new CountDecimateQueryable("fooproc", 2, 2, 3), list);
		CountDecimate cd = (CountDecimate) new CountDecimate(0).read(ior, map);
		assertNotNull(cd);
		assertEquals(3, cd.m_interval);
		assertEquals(2, cd.m_currentCount);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid1() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = SingleProcessorTest.getPrintedMap(1, 1, new CountDecimateQueryable("fooproc", 2, 2, 3), 3);
		new CountDecimate(0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid2() throws ReadException
	{
		List<Integer> list = new ArrayList<Integer>(1);
		list.add(3);
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = SingleProcessorTest.getPrintedMap(1, 1, new CountDecimateQueryable("fooproc", 2, 2, 3), list);
		new CountDecimate(0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid3() throws ReadException
	{
		List<Object> list = new ArrayList<Object>(2);
		list.add("foo");
		list.add(2);
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = SingleProcessorTest.getPrintedMap(1, 1, new CountDecimateQueryable("fooproc", 2, 2, 3), list);
		new CountDecimate(0).read(ior, map);
	}
	
	@Test
	public void testQueryableUpstream()
	{
		CountDecimate decim = new CountDecimate(3);
		CountDecimateQueryable cdq = (CountDecimateQueryable) decim.getQueryable();
		assertNotNull(cdq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(2), NthOutput.get(0));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) cdq.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode con = (ConcreteObjectNode) leaves.get(0);
		DesignatedObject dob = con.getDesignatedObject();
		assertEquals(cdq, dob.getObject());
		Designator des = dob.getDesignator();
		NthInput ni = (NthInput) des.peek();
		assertEquals(0, ni.getIndex());
		NthEvent ne = (NthEvent) des.tail().peek();
		assertEquals(6, ne.getIndex());
	}
	
	@Test
	public void testQueryableUpstreamUnknown()
	{
		CountDecimate decim = new CountDecimate(3);
		CountDecimateQueryable cdq = (CountDecimateQueryable) decim.getQueryable();
		assertNotNull(cdq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(NthOutput.get(2), NthOutput.get(0));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) cdq.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		assertTrue(leaves.get(0) instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableDownstream1()
	{
		CountDecimate decim = new CountDecimate(3);
		CountDecimateQueryable cdq = (CountDecimateQueryable) decim.getQueryable();
		assertNotNull(cdq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(3), NthInput.get(0));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) cdq.query(TraceabilityQuery.TaintQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode con = (ConcreteObjectNode) leaves.get(0);
		DesignatedObject dob = con.getDesignatedObject();
		assertEquals(cdq, dob.getObject());
		Designator des = dob.getDesignator();
		NthOutput ni = (NthOutput) des.peek();
		assertEquals(0, ni.getIndex());
		NthEvent ne = (NthEvent) des.tail().peek();
		assertEquals(1, ne.getIndex());
	}
	
	@Test
	public void testQueryableDownstream2()
	{
		CountDecimate decim = new CountDecimate(3);
		CountDecimateQueryable cdq = (CountDecimateQueryable) decim.getQueryable();
		assertNotNull(cdq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(2), NthInput.get(0));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) cdq.query(TraceabilityQuery.TaintQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode con = (ConcreteObjectNode) leaves.get(0);
		DesignatedObject dob = con.getDesignatedObject();
		assertEquals(cdq, dob.getObject());
		Designator des = dob.getDesignator();
		assertTrue(des instanceof Designator.Nothing);
	}
	
	@Test
	public void testQueryableDownstreamUnknown()
	{
		CountDecimate decim = new CountDecimate(3);
		CountDecimateQueryable cdq = (CountDecimateQueryable) decim.getQueryable();
		assertNotNull(cdq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(NthInput.get(2), NthInput.get(0));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) cdq.query(TraceabilityQuery.TaintQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		assertTrue(leaves.get(0) instanceof UnknownNode);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testQueryablePrint() throws PrintException
	{
		CountDecimate decim = new CountDecimate(3);
		CountDecimateQueryable cdq = (CountDecimateQueryable) decim.getQueryable();
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> printed = (Map<String,Object>) iop.print(cdq);
		int interval = (Integer) printed.get(ProcessorQueryable.s_contentsKey);
		assertEquals(3, interval);
	}
	
	@Test
	public void testQueryableRead() throws ReadException
	{
		Map<String,Object> printed = ProcessorQueryableTest.getPrintedMap("fooproc", 1, 1, 3);
		IdentityObjectReader ior = new IdentityObjectReader();
		CountDecimateQueryable cdq = (CountDecimateQueryable) new CountDecimateQueryable("fooproc", 1, 1, 3).read(ior, printed);
		assertNotNull(cdq);
		assertEquals(3, cdq.m_interval);
	}
	
	@Test(expected = ReadException.class)
	public void testQueryableReadInvalid() throws ReadException
	{
		Map<String,Object> printed = ProcessorQueryableTest.getPrintedMap("fooproc", 1, 1, "foo");
		IdentityObjectReader ior = new IdentityObjectReader();
		new CountDecimateQueryable("fooproc", 1, 1, 3).read(ior, printed);
	}
	
	@Test
	public void testQueryableDuplicate() throws PrintException
	{
		CountDecimate decim = new CountDecimate(3);
		CountDecimateQueryable cdq = (CountDecimateQueryable) decim.getQueryable();
		CountDecimateQueryable cdq_dup = cdq.duplicate(false);
		assertFalse(cdq == cdq_dup);
		assertEquals(cdq.m_interval, cdq_dup.m_interval);
	}
}