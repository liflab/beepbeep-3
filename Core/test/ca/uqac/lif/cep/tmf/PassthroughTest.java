package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Map;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor.NthEvent;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.ProcessorQueryableTest;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.SingleProcessorTest;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.cep.tmf.Passthrough.PassthroughQueryable;
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

public class PassthroughTest
{
	@Test
	public void testPush1()
	{
		Passthrough pt = new Passthrough();
		SinkLast sl = new SinkLast();
		Connector.connect(pt, sl);
		Pushable p1 = pt.getPushableInput();
		p1.push("foo");
		assertEquals("foo", sl.getLast());
		p1.push("bar");
		assertEquals("bar", sl.getLast());
	}
	
	@Test
	public void testPull1()
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1).loop(false);
		Passthrough pt = new Passthrough();
		Connector.connect(qs, pt);
		Pullable p1 = pt.getPullableOutput();
		assertTrue(p1.hasNext());
		assertEquals(2, p1.pull());
		assertTrue(p1.hasNext());
		assertEquals(7, p1.pull());
		assertTrue(p1.hasNext());
		assertEquals(1, p1.pull());
		assertFalse(p1.hasNext());
	}
	
	@Test
	public void testPushDuplicateState1()
	{
		Passthrough pt = new Passthrough();
		SinkLast sl = new SinkLast();
		Connector.connect(pt, sl);
		Pushable p1 = pt.getPushableInput();
		p1.push("foo");
		assertEquals("foo", sl.getLast());
		Passthrough pt2 = pt.duplicate(true);
		assertFalse(pt2 == pt);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Passthrough pt = new Passthrough();
		Map<String,Object> map = (Map<String,Object>) iop.print(pt);
		assertFalse(map.containsKey(SingleProcessor.s_contentsKey));
	}
	
	@Test
	public void testRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Map<String,Object> map = SingleProcessorTest.getPrintedMap(1, 1, new PassthroughQueryable("foo", 1, 1), null);
		Passthrough pt = (Passthrough) new Passthrough().read(ior, map);
		assertNotNull(pt);
	}
	
	@Test
	public void testQueryableUpstream()
	{
		Passthrough pt = new Passthrough(2);
		PassthroughQueryable ptq = (PassthroughQueryable) pt.getQueryable();
		assertNotNull(ptq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(3), NthOutput.get(1));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) ptq.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode con = (ConcreteObjectNode) leaves.get(0);
		DesignatedObject dob = con.getDesignatedObject();
		assertEquals(ptq, dob.getObject());
		Designator des = dob.getDesignator();
		NthInput ni = (NthInput) des.peek();
		assertEquals(1, ni.getIndex());
		NthEvent ne = (NthEvent) des.tail().peek();
		assertEquals(3, ne.getIndex());
	}
	
	@Test
	public void testQueryableUpstreamUnknown()
	{
		Passthrough pt = new Passthrough(2);
		PassthroughQueryable ptq = (PassthroughQueryable) pt.getQueryable();
		assertNotNull(ptq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(NthOutput.get(3), NthOutput.get(1));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) ptq.query(TraceabilityQuery.ProvenanceQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		assertTrue(leaves.get(0) instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableDownstream()
	{
		Passthrough pt = new Passthrough(2);
		PassthroughQueryable ptq = (PassthroughQueryable) pt.getQueryable();
		assertNotNull(ptq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(new NthEvent(3), NthInput.get(1));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) ptq.query(TraceabilityQuery.TaintQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode con = (ConcreteObjectNode) leaves.get(0);
		DesignatedObject dob = con.getDesignatedObject();
		assertEquals(ptq, dob.getObject());
		Designator des = dob.getDesignator();
		NthOutput ni = (NthOutput) des.peek();
		assertEquals(1, ni.getIndex());
		NthEvent ne = (NthEvent) des.tail().peek();
		assertEquals(3, ne.getIndex());
	}
	
	@Test
	public void testQueryableDownstreamUnknown()
	{
		Passthrough pt = new Passthrough(2);
		PassthroughQueryable ptq = (PassthroughQueryable) pt.getQueryable();
		assertNotNull(ptq);
		ConcreteTracer factory = new ConcreteTracer();
		ConcreteTraceabilityNode root = factory.getAndNode();
		ComposedDesignator cd = new ComposedDesignator(NthInput.get(3), NthInput.get(1));
		List<TraceabilityNode> leaves = (List<TraceabilityNode>) ptq.query(TraceabilityQuery.TaintQuery.instance, cd, root, factory);
		assertEquals(1, leaves.size());
		assertTrue(leaves.get(0) instanceof UnknownNode);
	}
	
	@Test
	public void testQueryableDuplicate()
	{
		Passthrough pt = new Passthrough(2);
		PassthroughQueryable ptq = (PassthroughQueryable) pt.getQueryable();
		assertNotNull(ptq);
		PassthroughQueryable ptq2 = ptq.duplicate(true);
		assertFalse(ptq2 == ptq);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testQueryablePrint() throws PrintException
	{
		Passthrough pt = new Passthrough(2);
		PassthroughQueryable ptq = (PassthroughQueryable) pt.getQueryable();
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> printed = (Map<String,Object>) ptq.print(iop);
		assertFalse(printed.containsKey(ProcessorQueryable.s_contentsKey));
	}
	
	@Test
	public void testQueryableRead() throws ReadException
	{
		Map<String,Object> printed = ProcessorQueryableTest.getPrintedMap("fooproc", 2, 2, null);
		IdentityObjectReader ior = new IdentityObjectReader();
		PassthroughQueryable ptq = (PassthroughQueryable) new PassthroughQueryable("", 0, 0).read(ior, printed);
		assertNotNull(ptq);
	}
}
