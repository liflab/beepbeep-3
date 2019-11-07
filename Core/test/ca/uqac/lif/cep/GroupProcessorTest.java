package ca.uqac.lif.cep;

import static org.junit.Assert.*;
import static ca.uqac.lif.cep.TestUtilities.verifyConnections;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.GroupProcessor.InputProxyConnection;
import ca.uqac.lif.cep.GroupProcessor.OutputProxyConnection;
import ca.uqac.lif.cep.GroupProcessor.ProcessorConnection;
import ca.uqac.lif.cep.Processor.ProcessorException;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.cep.TestUtilities.TestableSingleProcessor;
import ca.uqac.lif.cep.TestUtilities.TestableGroupProcessor;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.SinkLast;
import ca.uqac.lif.petitpoucet.common.Context;

import static ca.uqac.lif.cep.ProcessorTest.assertConnectedTo;
import static ca.uqac.lif.cep.ProcessorTest.assertNotConnectedTo;

@RunWith(JUnit4.class)
public class GroupProcessorTest 
{
	/**
	 * Checks the behaviour of a processor's {@link Context} object:
	 * <ul>
	 * <li>a key set with {@link Processor#setContext(String, Object)}
	 * can be retrieved with {@link Processor#getContext(String)}</li>
	 * <li>undefined keys return null</li>
	 * </ul>
	 */
	@Test
	public void testContext()
	{
		TestableGroupProcessor spw = new TestableGroupProcessor(1, 1);
		spw.setContext("foo", 10);
		assertEquals(10, spw.getContext("foo"));
		// Undefined keys return null
		assertNull(spw.getContext("bar"));
	}

	/**
	 * Checks that performing a stateful duplication of a processor:
	 * <ul>
	 * <li>results in a new processor whose context is a distinct object</li>
	 * <li>the context in the new processor has the same key-value pairs as
	 * the original</li>
	 * </ul>
	 */
	@Test
	public void testContextDuplicateState()
	{
		TestableGroupProcessor spw = new TestableGroupProcessor(1, 1);
		spw.setContext("foo", 10);
		TestableGroupProcessor spw2 = (TestableGroupProcessor) spw.duplicate(true);
		// Contexts are not shared objects
		assertFalse(spw.getContextMap() == spw2.getContextMap());
		// Context is preserved on stateful duplication
		assertEquals(10, spw2.getContext("foo"));
	}

	/**
	 * Checks that performing a stateless duplication of a processor:
	 * <ul>
	 * <li>results in a new processor whose context is a distinct object</li>
	 * <li>the context in the new processor is empty</li>
	 * </ul>
	 */
	@Test
	public void testContextDuplicateNoState()
	{
		TestableGroupProcessor spw = new TestableGroupProcessor(1, 1);
		spw.setContext("foo", 10);
		TestableGroupProcessor spw2 = (TestableGroupProcessor) spw.duplicate();
		// Contexts are not shared objects
		assertFalse(spw.getContextMap() == spw2.getContextMap());
		// Duplication without state wipes the context
		assertTrue(spw2.getContextMap().isEmpty());
	}
	
	@Test
	public void testPassthroughPull1()
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		{
			Passthrough pt = new Passthrough();
			gp.associateInput(0, pt, 0);
			gp.associateOutput(0, pt, 0);
			gp.add(pt);
		}
		QueueSource src1 = new QueueSource().setEvents(1, 2, 3, 4).loop(false);
		Connector.connect(src1, gp);
		Pullable p = gp.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals(1, p.pull());
		assertTrue(p.hasNext());
		assertEquals(2, p.pull());
		assertTrue(p.hasNext());
		assertEquals(3, p.pull());
		assertTrue(p.hasNext());
		assertEquals(4, p.pull());
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testPullable1()
	{
		GroupProcessor gp = new GroupProcessor(2, 2);
		Pullable p = gp.getPullableOutput(1);
		assertNotNull(p);
		assertNull(p.getType());
		assertTrue(p instanceof OutputProxyConnection);
		assertEquals(1, p.getIndex());
		assertEquals(gp, p.getObject());
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		spw.setOutputType(Number.class);
		gp.add(spw);
		gp.associateInput(0, spw, 0);
		gp.associateInput(1, spw, 1);
		gp.associateOutput(0, spw, 0);
		gp.associateOutput(1, spw, 1);
		assertEquals(Number.class, p.getType());
	}
	
	@Test
	public void testPushable1()
	{
		GroupProcessor gp = new GroupProcessor(2, 2);
		Pushable p = gp.getPushableInput(1);
		assertNotNull(p);
		assertNull(p.getType());
		assertTrue(p instanceof InputProxyConnection);
		assertEquals(1, p.getIndex());
		assertEquals(gp, p.getObject());
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		spw.setInputType(Number.class);
		gp.add(spw);
		gp.associateInput(0, spw, 0);
		gp.associateInput(1, spw, 1);
		gp.associateOutput(0, spw, 0);
		gp.associateOutput(1, spw, 1);
		assertEquals(Number.class, p.getType());
	}
	
	@SuppressWarnings("deprecation")
	@Test(expected = UnsupportedOperationException.class)
	public void testNotifySources()
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.notifySources(false);
	}
	
	@Test(expected = ProcessorException.class)
	public void testPullableException1()
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.getPullableOutput(1);
	}
	
	@Test(expected = ProcessorException.class)
	public void testPullableException2()
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Pullable p = spw.getPullableOutput();
		gp.setPullableInput(2, p);
	}
	
	@Test(expected = ProcessorException.class)
	public void testPullableException3()
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Pullable p = spw.getPullableOutput();
		gp.setToInput(2, p);
	}
	
	@Test(expected = ProcessorException.class)
	public void testPushableException1()
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		gp.getPushableInput(1);
	}
	
	@Test(expected = ProcessorException.class)
	public void testPushableException2()
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Pushable p = spw.getPushableInput();
		gp.setPushableOutput(2, p);
	}
	
	@Test(expected = ProcessorException.class)
	public void testPushableException3()
	{
		GroupProcessor gp = new GroupProcessor(1, 1);
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Pushable p = spw.getPushableInput();
		gp.setToOutput(2, p);
	}

	@Test
	public void testPassthroughDuplicate1()
	{
		GroupProcessor gp0 = new GroupProcessor(1, 1);
		{
			Passthrough pt = new Passthrough();
			gp0.associateInput(0, pt, 0);
			gp0.associateOutput(0, pt, 0);
			gp0.add(pt);
		}
		GroupProcessor gp = gp0.duplicate();
		QueueSource src1 = new QueueSource().setEvents(1, 2, 3, 4).loop(false);
		Connector.connect(src1, gp);
		Pullable p = gp.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals(1, p.pull());
		assertTrue(p.hasNext());
		assertEquals(2, p.pull());
		assertTrue(p.hasNext());
		assertEquals(3, p.pull());
		assertTrue(p.hasNext());
		assertEquals(4, p.pull());
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testInitializationUnary()
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		Set<Processor> gp_ip = gp.getProcessors();
		assertTrue(gp_ip.isEmpty());
		Pushable psh = gp.getPushableInput();
		assertNotNull(psh);
		assertTrue(psh instanceof InputProxyConnection);
		InputProxyConnection ipc = (InputProxyConnection) psh;
		assertNull(ipc.m_pullable);
		assertNull(ipc.m_pushable);
		assertEquals(0, ipc.getIndex());
		Pullable pll = gp.getPullableOutput();
		assertNotNull(pll);
		assertTrue(pll instanceof OutputProxyConnection);
		OutputProxyConnection opc = (OutputProxyConnection) pll;
		assertNull(opc.m_pullable);
		assertNull(opc.m_pushable);
		assertEquals(0, opc.getIndex());
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		gp.add(spw);
		// The added processor is not a source
		assertEquals(1, gp_ip.size());
		assertTrue(gp_ip.contains(spw));
		gp.associateInput(0, spw, 0);
		assertNull(ipc.m_pullable);
		assertNotNull(ipc.m_pushable);
		assertEquals(spw.getPushableInput(0), ipc.m_pushable);
		// Check that this does not touch the output
		assertNull(opc.m_pullable);
		assertNull(opc.m_pushable);
		gp.associateOutput(0, spw, 0);
		assertNotNull(opc.m_pullable);
		assertEquals(spw.getPullableOutput(0), opc.m_pullable);
		assertNull(opc.m_pushable);
		// Connect something to the input
		TestableSingleProcessor spw_up = new TestableSingleProcessor(1, 1);
		Connector.connect(spw_up, gp);
		assertNotNull(ipc.m_pullable);
		assertEquals(spw_up.getPullableOutput(0), ipc.m_pullable);
		assertNull(opc.m_pushable);
		// Connect something to the output
		TestableSingleProcessor spw_dn = new TestableSingleProcessor(1, 1);
		Connector.connect(gp, spw_dn);
		assertNotNull(opc.m_pushable);
		assertEquals(spw_dn.getPushableInput(0), opc.m_pushable);
	}
	
	@Test
	public void testAddMultiple()
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		Set<Processor> procs = new HashSet<Processor>(3);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw3 = new TestableSingleProcessor(1, 1);
		procs.add(spw1);
		procs.add(spw2);
		procs.add(spw3);
		gp.add(procs);
		Set<Processor> set_procs = gp.getProcessors();
		// When adding a collection, the group's inner set is not the
		// collection we pass as the argument to add
		assertFalse(set_procs == procs);
		assertTrue(set_procs.contains(spw1));
		assertTrue(set_procs.contains(spw2));
		assertTrue(set_procs.contains(spw3));
	}
	
	@SuppressWarnings("deprecation")
	@Test
	public void testAddMultiple2()
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		Set<Processor> procs = new HashSet<Processor>(3);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw3 = new TestableSingleProcessor(1, 1);
		gp.addProcessors(spw1, spw2, spw3);
		Set<Processor> set_procs = gp.getProcessors();
		// When adding a collection, the group's inner set is not the
		// collection we pass as the argument to add
		assertFalse(set_procs == procs);
		assertTrue(set_procs.contains(spw1));
		assertTrue(set_procs.contains(spw2));
		assertTrue(set_procs.contains(spw3));
	}
	
	@Test
	public void testStart()
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		Set<Processor> procs = new HashSet<Processor>(3);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw3 = new TestableSingleProcessor(1, 1);
		procs.add(spw1);
		procs.add(spw2);
		procs.add(spw3);
		gp.add(procs);
		gp.start();
		assertEquals(1, spw1.getCallsToStart());
		assertEquals(1, spw2.getCallsToStart());
		assertEquals(1, spw3.getCallsToStart());
	}
	
	@Test
	public void testStop()
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		Set<Processor> procs = new HashSet<Processor>(3);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw3 = new TestableSingleProcessor(1, 1);
		procs.add(spw1);
		procs.add(spw2);
		procs.add(spw3);
		gp.add(procs);
		gp.stop();
		assertEquals(1, spw1.getCallsToStop());
		assertEquals(1, spw2.getCallsToStop());
		assertEquals(1, spw3.getCallsToStop());
	}
	
	@Test
	public void testPassthroughUnaryPull()
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		Set<Processor> gp_ip = gp.getProcessors();
		assertTrue(gp_ip.isEmpty());
		TestableSingleProcessor pt = new TestableSingleProcessor(1, 1);
		gp.associateInput(0, pt, 0);
		gp.associateOutput(0, pt, 0);
		gp.add(pt);
		assertEquals(1, gp_ip.size());
		assertTrue(gp_ip.contains(pt));
		QueueSource src1 = new QueueSource().setEvents(1, 2, 10).loop(false);
		Connector.connect(src1, gp);
		Pullable p = gp.getPullableOutput();
		assertEquals(p, gp.getPullableOutput());
		assertEquals(0, p.getIndex());
		assertEquals(gp, p.getObject());
		assertTrue(p.hasNext());
		assertEquals(1, p.next());
		assertTrue(p.hasNext());
		assertEquals(2, p.next());
		assertTrue(p.hasNext());
		assertEquals(10, p.next());
		assertFalse(p.hasNext());
	}
	
	@Test(expected = ProcessorException.class)
	public void testPassthroughUnaryPullException()
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor pt = new TestableSingleProcessor(1, 1);
		gp.associateInput(0, pt, 0);
		gp.associateOutput(0, pt, 0);
		gp.add(pt);
		QueueSource src1 = new QueueSource().setEvents(1).loop(false);
		Connector.connect(src1, gp);
		Pullable p = gp.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals(1, p.next());
		assertFalse(p.hasNext());
		p.pull();
	}
	
	@Test
	public void testPassthroughUnaryPush()
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor pt = new TestableSingleProcessor(1, 1);
		Queue<Object[]> fronts = pt.getFronts();
		gp.associateInput(0, pt, 0);
		gp.associateOutput(0, pt, 0);
		SinkLast sl = new SinkLast();
		Connector.connect(gp, sl);
		Pushable p = gp.getPushableInput();
		assertEquals(p, gp.getPushableInput());
		assertEquals(0, p.getIndex());
		assertEquals(gp, p.getObject());
		p.push("foo");
		assertEquals("foo", sl.getLast());
		assertEquals(1, fronts.size());
		p.end();
		assertEquals(1, fronts.size());
		assertEquals(1, pt.getCallsToEnd());
		p.end();
		assertEquals(1, fronts.size());
		assertEquals(1, pt.getCallsToEnd());
	}
	
	/**
	 * Checks that trying to duplicate a processor chain that is not
	 * connected throws an exception
	 */
	@Test(expected = ProcessorException.class)
	public void testDisconnectedDuplicate()
	{
		TestableGroupProcessor gpw = new TestableGroupProcessor(1, 1);
		gpw.add(new TestableSingleProcessor(1, 1), new TestableSingleProcessor(1, 1));
		gpw.duplicate();
	}
	
	@Test
	public void testReset()
	{
		TestableGroupProcessor gpw = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		Connector.connect(spw1, spw2);
		gpw.add(spw1, spw2);
		gpw.associateInput(0, spw1, 0);
		gpw.associateOutput(0, spw2, 0);
		assertEquals(0, spw1.getCallsToReset());
		assertEquals(0, spw2.getCallsToReset());
		gpw.reset();
		assertEquals(1, spw1.getCallsToReset());
		assertEquals(1, spw2.getCallsToReset());
		gpw.reset();
		assertEquals(2, spw1.getCallsToReset());
		assertEquals(2, spw2.getCallsToReset());
	}
	
	@Test
	public void testDuplicateChainState()
	{
		TestableGroupProcessor gpw = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		spw1.setContext("foo1", "bar1");
		spw2.setContext("foo2", "bar2");
		Connector.connect(spw1, spw2);
		gpw.add(spw1, spw2);
		gpw.associateInput(0, spw1, 0);
		gpw.associateOutput(0, spw2, 0);
		TestableGroupProcessor gpw_d = (TestableGroupProcessor) gpw.duplicate(true);
		assertNotNull(gpw_d);
		assertFalse(gpw.m_innerProcessors == gpw_d.m_innerProcessors);
		Map<Processor,Processor> correspondences = gpw.m_correspondences;
		TestableSingleProcessor spw1_d = (TestableSingleProcessor) correspondences.get(spw1);
		TestableSingleProcessor spw2_d = (TestableSingleProcessor) correspondences.get(spw2);
		assertEquals("bar1", spw1_d.getContext("foo1"));
		assertEquals("bar2", spw2_d.getContext("foo2"));
		assertConnectedTo(spw1_d, 0, spw2_d, 0);
		assertNotConnectedTo(spw2_d, 0, spw1_d, 0);
		InputProxyConnection ipc = (InputProxyConnection) gpw_d.getPushableInput(0);
		assertEquals(ipc, spw1_d.getInputConnection(0));
		OutputProxyConnection opc = (OutputProxyConnection) gpw_d.getPullableOutput(0);
		assertEquals(spw2_d.getOutputConnection(0), opc);
	}
	
	@Test
	public void testDuplicateChainNoState()
	{
		TestableGroupProcessor gpw = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		spw1.setContext("foo1", "bar1");
		spw2.setContext("foo2", "bar2");
		Connector.connect(spw1, spw2);
		gpw.add(spw1, spw2);
		gpw.associateInput(0, spw1, 0);
		gpw.associateOutput(0, spw2, 0);
		TestableGroupProcessor gpw_d = (TestableGroupProcessor) gpw.duplicate(false);
		assertNotNull(gpw_d);
		assertFalse(gpw.m_innerProcessors == gpw_d.m_innerProcessors);
		Map<Processor,Processor> correspondences = gpw.m_correspondences;
		TestableSingleProcessor spw1_d = (TestableSingleProcessor) correspondences.get(spw1);
		TestableSingleProcessor spw2_d = (TestableSingleProcessor) correspondences.get(spw2);
		assertNull("bar1", spw1_d.getContext("foo1"));
		assertNull("bar2", spw2_d.getContext("foo2"));
		assertConnectedTo(spw1_d, 0, spw2_d, 0);
		assertNotConnectedTo(spw2_d, 0, spw1_d, 0);
		InputProxyConnection ipc = (InputProxyConnection) gpw_d.getPushableInput(0);
		assertEquals(ipc, spw1_d.getInputConnection(0));
		OutputProxyConnection opc = (OutputProxyConnection) gpw_d.getPullableOutput(0);
		assertEquals(spw2_d.getOutputConnection(0), opc);
	}
	
	@Test
	public void testConnectUpstream()
	{
		QueueSource src1 = new QueueSource().setEvents(3, 4, 5);
		QueueSource src2 = new QueueSource().setEvents(10, 11, 12);
		TestableGroupProcessor gpw = new TestableGroupProcessor(2, 2);
		Connector.connect(src1, 0, gpw, 0);
		Connector.connect(src2, 0, gpw, 1);
		Pullable p1 = (Pullable) gpw.getInputConnection(0);
		assertEquals(src1, p1.getObject());
		assertEquals(0, p1.getIndex());
		Pullable p2 = (Pullable) gpw.getInputConnection(1);
		assertEquals(src2, p2.getObject());
		assertEquals(0, p2.getIndex());
	}
	
	@Test
	public void testConnectDownstream()
	{
		SinkLast src1 = new SinkLast();
		SinkLast src2 = new SinkLast();
		TestableGroupProcessor gpw = new TestableGroupProcessor(2, 2);
		Connector.connect(gpw, 0, src1, 0);
		Connector.connect(gpw, 1, src2, 0);
		Pushable p1 = (Pushable) gpw.getOutputConnection(0);
		assertEquals(src1, p1.getObject());
		assertEquals(0, p1.getIndex());
		Pushable p2 = (Pushable) gpw.getOutputConnection(1);
		assertEquals(src2, p2.getObject());
		assertEquals(0, p2.getIndex());
	}
	
	@Test(expected = ProcessorException.class)
	public void testInputConnectionOutOfBounds()
	{
		QueueSource src1 = new QueueSource().setEvents(3, 4, 5);
		TestableGroupProcessor gpw = new TestableGroupProcessor(1, 1);
		Connector.connect(src1, 0, gpw, 0);
		gpw.getInputConnection(1);
	}
	
	@Test(expected = ProcessorException.class)
	public void testOutputConnectionOutOfBounds()
	{
		SinkLast src1 = new SinkLast();
		TestableGroupProcessor gpw = new TestableGroupProcessor(1, 1);
		Connector.connect(gpw, 0, src1, 0);
		gpw.getOutputConnection(1);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint1() throws PrintException
	{
		GroupProcessor gp = new GroupProcessor(3, 2);
		gp.setContext("foo", "bar");
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> map = (Map<String,Object>) iop.print(gp);
		assertEquals(4, map.size());
		assertTrue(map.containsKey(GroupProcessor.s_arityKey));
		assertTrue(map.containsKey(GroupProcessor.s_connectionsKey));
		assertTrue(map.containsKey(GroupProcessor.s_processorsKey));
		assertTrue(map.containsKey(GroupProcessor.s_contextKey));
		List<?> arity = (List<?>) map.get(GroupProcessor.s_arityKey);
		assertEquals(2, arity.size());
		assertEquals(3, ((Integer) arity.get(0)).intValue());
		assertEquals(2, ((Integer) arity.get(1)).intValue());
		List<?> procs = (List<?>) map.get(GroupProcessor.s_processorsKey);
		assertEquals(0, procs.size());
		List<?> connections = (List<?>) map.get(GroupProcessor.s_connectionsKey);
		assertEquals(0, connections.size());
		Map<String,Object> c = (Map<String,Object>) map.get(GroupProcessor.s_contextKey);
		assertEquals(1, c.size());
		assertEquals("bar", c.get("foo"));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint2() throws PrintException
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor sp = new TestableSingleProcessor(1, 1);
		gp.add(sp);
		gp.associateInput(0, sp, 0);
		gp.associateOutput(0, sp, 0);
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> map = (Map<String,Object>) iop.print(gp);
		assertEquals(4, map.size());
		assertTrue(map.containsKey(GroupProcessor.s_arityKey));
		assertTrue(map.containsKey(GroupProcessor.s_connectionsKey));
		assertTrue(map.containsKey(GroupProcessor.s_processorsKey));
		assertTrue(map.containsKey(GroupProcessor.s_contextKey));
		List<?> arity = (List<?>) map.get(GroupProcessor.s_arityKey);
		assertEquals(2, arity.size());
		assertEquals(1, ((Integer) arity.get(0)).intValue());
		assertEquals(1, ((Integer) arity.get(1)).intValue());
		List<?> procs = (List<?>) map.get(GroupProcessor.s_processorsKey);
		assertEquals(1, procs.size());
		List<?> connections = (List<?>) map.get(GroupProcessor.s_connectionsKey);
		assertEquals(2, connections.size());
		List<Processor> proc_list = gp.getProcessorList();
		verifyConnections(gp, proc_list, (List<ProcessorConnection>) connections);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint3() throws PrintException
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor sp1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor sp2 = new TestableSingleProcessor(1, 1);
		Connector.connect(sp1, sp2);
		gp.add(sp1, sp2);
		gp.associateInput(0, sp1, 0);
		gp.associateOutput(0, sp2, 0);
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> map = (Map<String,Object>) iop.print(gp);
		assertEquals(4, map.size());
		assertTrue(map.containsKey(GroupProcessor.s_arityKey));
		assertTrue(map.containsKey(GroupProcessor.s_connectionsKey));
		assertTrue(map.containsKey(GroupProcessor.s_processorsKey));
		assertTrue(map.containsKey(GroupProcessor.s_contextKey));
		List<?> arity = (List<?>) map.get(GroupProcessor.s_arityKey);
		assertEquals(2, arity.size());
		assertEquals(1, ((Integer) arity.get(0)).intValue());
		assertEquals(1, ((Integer) arity.get(1)).intValue());
		List<?> procs = (List<?>) map.get(GroupProcessor.s_processorsKey);
		assertEquals(2, procs.size());
		List<?> connections = (List<?>) map.get(GroupProcessor.s_connectionsKey);
		List<Processor> proc_list = gp.getProcessorList();
		assertEquals(3, connections.size());
		verifyConnections(gp, proc_list, (List<ProcessorConnection>) connections);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrintDisconnected1() throws PrintException
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor sp1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor sp2 = new TestableSingleProcessor(1, 1);
		Connector.connect(sp1, sp2);
		gp.add(sp1, sp2);
		gp.associateOutput(0, sp2, 0);
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> map = (Map<String,Object>) iop.print(gp);
		assertEquals(4, map.size());
		assertTrue(map.containsKey(GroupProcessor.s_arityKey));
		assertTrue(map.containsKey(GroupProcessor.s_connectionsKey));
		assertTrue(map.containsKey(GroupProcessor.s_processorsKey));
		assertTrue(map.containsKey(GroupProcessor.s_contextKey));
		List<?> arity = (List<?>) map.get(GroupProcessor.s_arityKey);
		assertEquals(2, arity.size());
		assertEquals(1, ((Integer) arity.get(0)).intValue());
		assertEquals(1, ((Integer) arity.get(1)).intValue());
		List<?> procs = (List<?>) map.get(GroupProcessor.s_processorsKey);
		assertEquals(2, procs.size());
		List<?> connections = (List<?>) map.get(GroupProcessor.s_connectionsKey);
		List<Processor> proc_list = gp.getProcessorList();
		assertEquals(2, connections.size());
		verifyConnections(gp, proc_list, (List<ProcessorConnection>) connections);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrintDisconnected2() throws PrintException
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor sp1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor sp2 = new TestableSingleProcessor(1, 1);
		Connector.connect(sp1, sp2);
		gp.add(sp1, sp2);
		gp.associateInput(0, sp1, 0);
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> map = (Map<String,Object>) iop.print(gp);
		assertEquals(4, map.size());
		assertTrue(map.containsKey(GroupProcessor.s_arityKey));
		assertTrue(map.containsKey(GroupProcessor.s_connectionsKey));
		assertTrue(map.containsKey(GroupProcessor.s_processorsKey));
		assertTrue(map.containsKey(GroupProcessor.s_contextKey));
		List<?> arity = (List<?>) map.get(GroupProcessor.s_arityKey);
		assertEquals(2, arity.size());
		assertEquals(1, ((Integer) arity.get(0)).intValue());
		assertEquals(1, ((Integer) arity.get(1)).intValue());
		List<?> procs = (List<?>) map.get(GroupProcessor.s_processorsKey);
		assertEquals(2, procs.size());
		List<?> connections = (List<?>) map.get(GroupProcessor.s_connectionsKey);
		List<Processor> proc_list = gp.getProcessorList();
		assertEquals(2, connections.size());
		verifyConnections(gp, proc_list, (List<ProcessorConnection>) connections);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrintDisconnected3() throws PrintException
	{
		TestableGroupProcessor gp = new TestableGroupProcessor(1, 1);
		TestableSingleProcessor sp1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor sp2 = new TestableSingleProcessor(1, 1);
		gp.add(sp1, sp2);
		gp.associateInput(0, sp1, 0);
		gp.associateOutput(0, sp2, 0);
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> map = (Map<String,Object>) iop.print(gp);
		assertEquals(4, map.size());
		assertTrue(map.containsKey(GroupProcessor.s_arityKey));
		assertTrue(map.containsKey(GroupProcessor.s_connectionsKey));
		assertTrue(map.containsKey(GroupProcessor.s_processorsKey));
		assertTrue(map.containsKey(GroupProcessor.s_contextKey));
		List<?> arity = (List<?>) map.get(GroupProcessor.s_arityKey);
		assertEquals(2, arity.size());
		assertEquals(1, ((Integer) arity.get(0)).intValue());
		assertEquals(1, ((Integer) arity.get(1)).intValue());
		List<?> procs = (List<?>) map.get(GroupProcessor.s_processorsKey);
		assertEquals(2, procs.size());
		List<?> connections = (List<?>) map.get(GroupProcessor.s_connectionsKey);
		List<Processor> proc_list = gp.getProcessorList();
		assertEquals(2, connections.size());
		verifyConnections(gp, proc_list, (List<ProcessorConnection>) connections);
	}
	
	
	
	@Test
	public void testRead1() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		List<Integer> arity = new ArrayList<Integer>(2);
		arity.add(3);
		arity.add(2);
		map.put(GroupProcessor.s_arityKey, arity);
		List<Object> procs = new ArrayList<Object>(0);
		map.put(GroupProcessor.s_processorsKey, procs);
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>(0);
		map.put(GroupProcessor.s_connectionsKey, connections);
		Context c = new Context();
		c.put("foo", "bar");
		map.put(GroupProcessor.s_contextKey, c);
		IdentityObjectReader ior = new IdentityObjectReader();
		TestableGroupProcessor gpw = (TestableGroupProcessor) new TestableGroupProcessor(0, 0).read(ior, map);
		assertNotNull(gpw);
		assertEquals(3, gpw.getInputArity());
		assertEquals(2, gpw.getOutputArity());
		assertEquals(0, gpw.m_innerProcessors.size());
		assertEquals("bar", gpw.getContext("foo"));
	}
	
	@Test
	public void testRead2() throws ReadException, PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		Context c = new Context();
		c.put("foo", "bar");
		map.put(GroupProcessor.s_contextKey, c);
		List<Integer> arity = new ArrayList<Integer>(2);
		arity.add(1);
		arity.add(1);
		map.put(GroupProcessor.s_arityKey, arity);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		List<Processor> procs = new ArrayList<Processor>(1);
		procs.add(spw1);
		procs.add(spw2);
		map.put(GroupProcessor.s_processorsKey, procs);
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>(2);
		connections.add(new ProcessorConnection(-1, 0, 0, 0));
		connections.add(new ProcessorConnection(0, 0, 1, 0));
		connections.add(new ProcessorConnection(1, 0, -1, 0));
		map.put(GroupProcessor.s_connectionsKey, connections);
		IdentityObjectReader ior = new IdentityObjectReader();
		TestableGroupProcessor gpw = (TestableGroupProcessor) new TestableGroupProcessor(0, 0).read(ior, map);
		assertNotNull(gpw);
		assertEquals(1, gpw.getInputArity());
		assertEquals(1, gpw.getOutputArity());
		assertEquals(2, gpw.m_innerProcessors.size());
		assertTrue(gpw.m_innerProcessors.contains(spw1));
		assertTrue(gpw.m_innerProcessors.contains(spw2));
		verifyConnections(gpw, procs, connections);
		assertEquals("bar", gpw.getContext("foo"));
	}
	
	/**
	 * Checks that deserializing with a missing key in the map throws an
	 * exception.
	 * @throws ReadException
	 * @throws PrintException
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid1() throws ReadException, PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(GroupProcessor.s_contextKey, new Context());
		List<Integer> arity = new ArrayList<Integer>(2);
		arity.add(1);
		arity.add(1);
		map.put(GroupProcessor.s_arityKey, arity);
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>(2);
		connections.add(new ProcessorConnection(-1, 0, 0, 0));
		connections.add(new ProcessorConnection(0, 0, 1, 0));
		connections.add(new ProcessorConnection(1, 0, -1, 0));
		map.put(GroupProcessor.s_connectionsKey, connections);
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableGroupProcessor(0, 0).read(ior, map);
	}
	
	/**
	 * Checks that the deserialization throws an exception if one of the
	 * connections refers to a non-existent processor index
	 * @throws ReadException
	 * @throws PrintException
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid2() throws ReadException, PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(GroupProcessor.s_contextKey, new Context());
		List<Integer> arity = new ArrayList<Integer>(2);
		arity.add(1);
		arity.add(1);
		map.put(GroupProcessor.s_arityKey, arity);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		List<Processor> procs = new ArrayList<Processor>(1);
		procs.add(spw1);
		procs.add(spw2);
		map.put(GroupProcessor.s_processorsKey, procs);
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>(2);
		connections.add(new ProcessorConnection(-1, 0, 0, 0));
		connections.add(new ProcessorConnection(0, 0, 3, 0)); // The error is 3 here
		connections.add(new ProcessorConnection(1, 0, -1, 0));
		map.put(GroupProcessor.s_connectionsKey, connections);
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableGroupProcessor(0, 0).read(ior, map);
	}
	
	/**
	 * Checks that deserializing something that is not a map throws
	 * exception.
	 * @throws ReadException
	 * @throws PrintException
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid3() throws ReadException, PrintException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableGroupProcessor(0, 0).read(ior, 3);
	}
	
	/**
	 * Checks that the deserialization throws an exception if one of the
	 * connections to the group's input refers to a non-existent processor index
	 * @throws ReadException
	 * @throws PrintException
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid4() throws ReadException, PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(GroupProcessor.s_contextKey, new Context());
		List<Integer> arity = new ArrayList<Integer>(2);
		arity.add(1);
		arity.add(1);
		map.put(GroupProcessor.s_arityKey, arity);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		List<Processor> procs = new ArrayList<Processor>(1);
		procs.add(spw1);
		procs.add(spw2);
		map.put(GroupProcessor.s_processorsKey, procs);
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>(2);
		connections.add(new ProcessorConnection(-1, 0, 3, 0)); // The error is 3 here
		connections.add(new ProcessorConnection(0, 0, 1, 0));
		connections.add(new ProcessorConnection(1, 0, -1, 0));
		map.put(GroupProcessor.s_connectionsKey, connections);
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableGroupProcessor(0, 0).read(ior, map);
	}
	
	/**
	 * Checks that the deserialization throws an exception if one of the
	 * connections to the group's output refers to a non-existent processor index
	 * @throws ReadException
	 * @throws PrintException
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid5() throws ReadException, PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(GroupProcessor.s_contextKey, new Context());
		List<Integer> arity = new ArrayList<Integer>(2);
		arity.add(1);
		arity.add(1);
		map.put(GroupProcessor.s_arityKey, arity);
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		List<Processor> procs = new ArrayList<Processor>(1);
		procs.add(spw1);
		procs.add(spw2);
		map.put(GroupProcessor.s_processorsKey, procs);
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>(2);
		connections.add(new ProcessorConnection(-1, 0, 0, 0));
		connections.add(new ProcessorConnection(0, 0, 1, 0));
		connections.add(new ProcessorConnection(3, 0, -1, 0)); // The error is 3 here
		map.put(GroupProcessor.s_connectionsKey, connections);
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableGroupProcessor(0, 0).read(ior, map);
	}
	
	/**
	 * Checks that the deserialization throws an exception if one of the
	 * map's elements does not have the expected type
	 * @throws ReadException
	 * @throws PrintException
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid6() throws ReadException, PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(GroupProcessor.s_contextKey, new Context());
		map.put(GroupProcessor.s_arityKey, 3); // Error is here: should be a list
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		List<Processor> procs = new ArrayList<Processor>(1);
		procs.add(spw1);
		procs.add(spw2);
		map.put(GroupProcessor.s_processorsKey, procs);
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>(2);
		connections.add(new ProcessorConnection(-1, 0, 0, 0));
		connections.add(new ProcessorConnection(0, 0, 1, 0));
		connections.add(new ProcessorConnection(1, 0, -1, 0));
		map.put(GroupProcessor.s_connectionsKey, connections);
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableGroupProcessor(0, 0).read(ior, map);
	}
	
	/**
	 * Checks that deserializing with a null value in the map throws an
	 * exception.
	 * @throws ReadException
	 * @throws PrintException
	 */
	@Test(expected = ReadException.class)
	public void testReadInvalid7() throws ReadException, PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(GroupProcessor.s_contextKey, new Context());
		map.put(GroupProcessor.s_processorsKey, null);
		map.put(GroupProcessor.s_contextKey, new Context());
		List<Integer> arity = new ArrayList<Integer>(2);
		arity.add(1);
		arity.add(1);
		map.put(GroupProcessor.s_arityKey, arity);
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>(2);
		connections.add(new ProcessorConnection(-1, 0, 0, 0));
		connections.add(new ProcessorConnection(0, 0, 1, 0));
		connections.add(new ProcessorConnection(1, 0, -1, 0));
		map.put(GroupProcessor.s_connectionsKey, connections);
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableGroupProcessor(0, 0).read(ior, map);
	}
	
	@Test
	public void testPrintConnection1() throws PrintException
	{
		ProcessorConnection pc = new ProcessorConnection(2, 7, 1, 8);
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Object o = iop.print(pc);
		assertTrue(o instanceof List);
		List<?> list = (List<?>) o;
		assertEquals(2, ((Integer) list.get(0)).intValue());
		assertEquals(7, ((Integer) list.get(1)).intValue());
		assertEquals(1, ((Integer) list.get(2)).intValue());
		assertEquals(8, ((Integer) list.get(3)).intValue());
	}
	
	@Test
	public void testReadConnection1() throws ReadException
	{
		List<Integer> list = new ArrayList<Integer>(4);
		list.add(2);
		list.add(7);
		list.add(1);
		list.add(8);
		IdentityObjectReader ior = new IdentityObjectReader();
		ProcessorConnection pc = new ProcessorConnection(0, 0, 0, 0).read(ior, list);
		assertNotNull(pc);
		assertEquals(2, pc.m_sourceId);
		assertEquals(7, pc.m_sourceIndex);
		assertEquals(1, pc.m_destinationId);
		assertEquals(8, pc.m_destinationIndex);
	}
	
	@Test(expected = ReadException.class)
	public void testReadConnectionInvalid1() throws ReadException
	{
		List<Integer> list = new ArrayList<Integer>(4);
		list.add(2);
		list.add(7);
		list.add(1);
		IdentityObjectReader ior = new IdentityObjectReader();
		new ProcessorConnection(0, 0, 0, 0).read(ior, list);
	}
	
	@Test(expected = ReadException.class)
	public void testReadConnectionInvalid2() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		new ProcessorConnection(0, 0, 0, 0).read(ior, 3);
	}
	
	@Test
	public void testGetInstance()
	{
		GroupProcessor gp = new GroupProcessor(0, 0);
		GroupProcessor gp2 = gp.getInstance(2, 3);
		assertEquals(2, gp2.getInputArity());
		assertEquals(3, gp2.getOutputArity());
	}
}