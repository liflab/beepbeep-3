package ca.uqac.lif.cep;

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
import ca.uqac.lif.azrael.clone.ClonePrinter;
import ca.uqac.lif.azrael.clone.CloneReader;
import ca.uqac.lif.cep.Processor.ProcessorException;
import ca.uqac.lif.cep.Pullable.NextStatus;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.cep.TestUtilities.TestableSingleProcessor;
import ca.uqac.lif.cep.TestUtilities.StutteringQueueSource;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.tmf.BlackHole;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.SinkLast;
import ca.uqac.lif.cep.tmf.Window;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.petitpoucet.DesignatedObject;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.graph.ConcreteObjectNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;
import ca.uqac.lif.petitpoucet.graph.UnknownNode;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;

/**
 * Unit tests for the abstract {@link SingleProcessor} class.
 */
public class SingleProcessorTest
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
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
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
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		spw.setContext("foo", 10);
		TestableSingleProcessor spw2 = spw.duplicate(true);
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
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		spw.setContext("foo", 10);
		TestableSingleProcessor spw2 = (TestableSingleProcessor) spw.duplicate();
		// Contexts are not shared objects
		assertFalse(spw.getContextMap() == spw2.getContextMap());
		// Duplication without state wipes the context
		assertTrue(spw2.getContextMap().isEmpty());
	}

	/**
	 * Checks that asking for the input <tt>Pushable</tt> of a processor
	 * <i>p</i> returns an object:
	 * <ul>
	 * <li>non-null</li>
	 * <li>such that calling {@link Pushable#getIndex()} returns 0</li>
	 * <li>such that calling {@link Pushable#getObject()} returns a reference to
	 * the processor itself</li>
	 * <li>such that calling {@link Pushable#reset()} has no effect</li>
	 * <li>further calls to {@link Processor#getPushableInput()} return the
	 * same object</li>
	 * </ul>
	 */
	@Test
	public void testPushable1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Pushable p = spw.getPushableInput();
		assertNotNull(p);
		assertEquals(0, p.getIndex());
		assertEquals(spw, p.getObject());
		Pushable p2 = spw.getPushableInput();
		assertEquals(p, p2);
	}

	/**
	 * Checks that asking for the input <tt>Pushable</tt> of a processor
	 * <i>p</i> returns an object:
	 * <ul>
	 * <li>non-null</li>
	 * <li>such that calling {@link Pushable#getIndex()} returns <i>i</i></li>
	 * <li>such that calling {@link Pushable#getObject()} returns a reference to
	 * the processor itself</li>
	 * <li>further calls to {@link Processor#getPushableInput()} return the
	 * same object</li>
	 * </ul>
	 */
	@Test
	public void testPushable2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		assertNotNull(p1);
		assertEquals(0, p1.getIndex());
		assertEquals(spw, p1.getObject());
		assertNotNull(p2);
		assertEquals(1, p2.getIndex());
		assertEquals(spw, p2.getObject());
		Pushable p1_2 = spw.getPushableInput(0);
		assertEquals(p1, p1_2);
		Pushable p2_2 = spw.getPushableInput(1);
		assertEquals(p2, p2_2);
	}

	/**
	 * Checks that asking for an input <tt>Pushable</tt> of a processor
	 * <i>p</i> with an invalid index throws a {@link ProcessorException}
	 */
	@Test(expected = ProcessorException.class)
	public void testPushableException1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		spw.getPushableInput(1);
	}
	
	/**
	 * Checks that setting a an input <tt>Pullable</tt> of a processor
	 * <i>p</i> with an invalid index throws a {@link ProcessorException}
	 */
	@Test(expected = ProcessorException.class)
	public void testPushableException2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		Pullable p = spw.getPullableOutput(0);
		spw2.setToInput(1, p);
	}
	
	/**
	 * Checks that asking for a an input <tt>Pullable</tt> of a processor
	 * <i>p</i> with an invalid index throws a {@link ProcessorException}
	 */
	@Test(expected = ProcessorException.class)
	public void testPushableException3()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		Pullable p = spw.getPullableOutput(0);
		spw2.setToInput(0, p);
		assertEquals(p, spw2.getInputConnection(0));
		spw2.getInputConnection(2);
	}

	/**
	 * Checks that asking for the output <tt>Pullable</tt> of a processor
	 * <i>p</i> returns an object:
	 * <ul>
	 * <li>non-null</li>
	 * <li>such that calling {@link Pullable#getIndex()} returns 0</li>
	 * <li>such that calling {@link Pullable#getObject()} returns a reference to
	 * the processor itself</li>
	 * <li>such that calling {@link Pushable#reset()} has no effect</li>
	 * <li>further calls to {@link Processor#getPullableOutput()} return the
	 * same object</li>
	 * </ul>
	 */
	@Test
	public void testPullable1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Pullable p = spw.getPullableOutput();
		assertNotNull(p);
		assertEquals(0, p.getIndex());
		assertEquals(spw, p.getObject());
		Pullable p2 = spw.getPullableOutput();
		assertEquals(p, p2);
	}

	/**
	 * Checks that asking for the output <tt>Pullable</tt> of a processor
	 * <i>p</i> with a valid index <i>i</i> returns an object:
	 * <ul>
	 * <li>non-null</li>
	 * <li>such that calling {@link Pullable#getIndex()} returns <i>i</i></li>
	 * <li>such that calling {@link Pullable#getObject()} returns a reference to
	 * the processor itself</li>
	 * <li>further calls to {@link Processor#getPullableOutput()} return the
	 * same object</li>
	 * </ul>
	 */
	@Test
	public void testPullable2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		Pullable p1 = spw.getPullableOutput(0);
		Pullable p2 = spw.getPullableOutput(1);
		assertNotNull(p1);
		assertEquals(0, p1.getIndex());
		assertEquals(spw, p1.getObject());
		assertNotNull(p2);
		assertEquals(1, p2.getIndex());
		assertEquals(spw, p2.getObject());
		Pullable p1_2 = spw.getPullableOutput(0);
		Pullable p2_2 = spw.getPullableOutput(1);
		assertEquals(p1, p1_2);
		assertEquals(p2, p2_2);
	}

	/**
	 * Checks that asking for the output <tt>Pullable</tt> of a processor
	 * <i>p</i> with an invalid index throws a {@link ProcessorException}
	 */
	@Test(expected = ProcessorException.class)
	public void testPullableException()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		spw.getPullableOutput(1);
	}
	
	/**
	 * Checks that setting a an output <tt>Pushable</tt> of a processor
	 * <i>p</i> with an invalid index throws a {@link ProcessorException}
	 */
	@Test(expected = ProcessorException.class)
	public void testPullableException2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		Pushable p = spw2.getPushableInput(0);
		spw.setToOutput(1, p);
	}
	
	/**
	 * Checks that asking for a an input <tt>Pullable</tt> of a processor
	 * <i>p</i> with an invalid index throws a {@link ProcessorException}
	 */
	@Test(expected = ProcessorException.class)
	public void testPullableException3()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		Pushable p = spw2.getPushableInput(0);
		spw.setToOutput(0, p);
		assertEquals(p, spw.getOutputConnection(0));
		spw.getOutputConnection(2);
	}

	/**
	 * Checks the behavior of an unary synchronous processor in push mode.
	 * <ul>
	 * <li>Since the tested processor has a selectivity of 1 (i.e.
	 * produces one output event for each input event received), all queues
	 * are empty between calls to {@link Pushable#push(Object)}</li>
	 * <li>Each call to push results in exactly one call to
	 * {@link SingleProcessor#compute(Object[], Queue)}, which produces exactly
	 * one output front at a time</li>
	 * <li>The event processed by {@link SingleProcessor#compute(Object[], Queue)}
	 * is exactly the event that was given in the call to {@link Pushable#push(Object)}</li> 
	 * </ul>
	 */
	@Test
	public void testQueuesUnaryPush()
	{
		Object[] front;
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		BlackHole bh = new BlackHole();
		Connector.connect(spw, bh);
		Queue<Object[]> fronts = spw.getFronts();
		Pushable p1 = spw.getPushableInput(0);
		assertEquals(1, spw.getInputArity());
		assertEquals(1, spw.getOutputArity());
		assertTrue(spw.getInputQueue(0).isEmpty());
		assertTrue(spw.getOutputQueue(0).isEmpty());
		assertEquals(0, fronts.size());
		p1.push(0);
		assertTrue(spw.getInputQueue(0).isEmpty());
		assertTrue(spw.getOutputQueue(0).isEmpty());
		assertEquals(1, fronts.size());
		front = fronts.remove();
		assertEquals(1, front.length);
		assertEquals(0, front[0]);
		p1.push(7);
		assertTrue(spw.getInputQueue(0).isEmpty());
		assertTrue(spw.getOutputQueue(0).isEmpty());
		assertEquals(1, fronts.size());
		front = fronts.remove();
		assertEquals(1, front.length);
		assertEquals(7, front[0]);
		p1.push(1);
	}

	@Test
	public void testQueuesUnaryPull()
	{
		Object[] front;
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		StutteringQueueSource sq1 = new StutteringQueueSource();
		sq1.setEvents(3).loop(false);
		Connector.connect(sq1, spw);
		Queue<Object> iq1 = spw.getInputQueue(0);
		Queue<Object> oq1 = spw.getOutputQueue(0);
		Queue<Object[]> fronts = spw.getFronts();
		Pullable p1 = spw.getPullableOutput(0);
		assertEquals(0, iq1.size());
		assertEquals(0, oq1.size());
		assertEquals(0, fronts.size());
		assertTrue(p1.hasNext());
		// Calling hasNext fetches an event from upstream
		assertEquals(1, sq1.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(1, oq1.size());
		assertEquals(3, oq1.peek());
		assertEquals(1, fronts.size());
		front = fronts.remove();
		assertEquals(1, front.length);
		assertEquals(3, front[0]);
		Object o = p1.pull();
		assertEquals(3, o);
		assertEquals(1, sq1.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(0, oq1.size());
		assertEquals(0, fronts.size());
		assertFalse(p1.hasNext());
		assertEquals(1, sq1.getComputeCount());
		assertFalse(p1.hasNext());
		assertEquals(1, sq1.getComputeCount());
	}

	@Test(expected = ProcessorException.class)
	public void testQueuesUnaryPullException()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		StutteringQueueSource sq1 = new StutteringQueueSource();
		sq1.setEvents(3).loop(false);
		Connector.connect(sq1, spw);
		Pullable p1 = spw.getPullableOutput(0);
		assertTrue(p1.hasNext());
		assertEquals(3, p1.next());
		assertFalse(p1.hasNext());
		// Should throw an exception
		p1.pull();
	}

	@Test
	public void testQueuesUnaryPullDecimate()
	{
		Object[] front;
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		StutteringQueueSource sq1 = new StutteringQueueSource();
		sq1.setStutterAmount(-2);
		sq1.setEvents(3, 1, 4, 1, 5);
		Connector.connect(sq1, spw);
		Queue<Object> iq1 = spw.getInputQueue(0);
		Queue<Object> oq1 = spw.getOutputQueue(0);
		Queue<Object[]> fronts = spw.getFronts();
		Pullable p1 = spw.getPullableOutput(0);
		assertEquals(0, iq1.size());
		assertEquals(0, oq1.size());
		assertEquals(0, fronts.size());
		assertTrue(p1.hasNext());
		// Asking hasNext to the source required two calls to compute
		assertEquals(2, sq1.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(1, oq1.size());
		assertEquals(3, oq1.peek());
		assertEquals(1, fronts.size());
		front = fronts.remove();
		assertEquals(1, front.length);
		assertEquals(3, front[0]);
		Object o = p1.pull();
		assertEquals(3, o);
		// Pulling from the source does not re-call compute
		assertEquals(2, sq1.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(0, oq1.size());
		assertEquals(0, fronts.size());
	}

	@Test
	public void testQueuesBinaryPullDecimate()
	{
		Object[] front;
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		StutteringQueueSource sq1 = new StutteringQueueSource();
		sq1.setStutterAmount(-2);
		sq1.setEvents(3, 1, 4, 1, 5).loop(false);
		StutteringQueueSource sq2 = new StutteringQueueSource();
		sq2.setStutterAmount(1);
		sq2.setEvents(2).loop(false);
		Connector.connect(sq1, 0, spw, 0);
		Connector.connect(sq2, 0, spw, 1);
		Queue<Object> iq1 = spw.getInputQueue(0);
		Queue<Object> iq2 = spw.getInputQueue(1);
		Queue<Object> oq1 = spw.getOutputQueue(0);
		Queue<Object> oq2 = spw.getOutputQueue(1);
		Queue<Object[]> fronts = spw.getFronts();
		Pullable p1 = spw.getPullableOutput(0);
		Pullable p2 = spw.getPullableOutput(0);
		assertEquals(0, iq1.size());
		assertEquals(0, iq2.size());
		assertEquals(0, oq1.size());
		assertEquals(0, oq2.size());
		assertEquals(0, fronts.size());
		assertTrue(p1.hasNext());
		// Asking hasNext to the source required two calls to compute on sq1
		assertEquals(2, sq1.getComputeCount());
		// Asking hasNext to the source required one call to compute on sq2
		assertEquals(1, sq2.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(1, oq1.size());
		assertEquals(3, oq1.peek());
		assertEquals(1, oq2.size());
		assertEquals(2, oq2.peek());
		assertEquals(1, fronts.size());
		front = fronts.remove();
		assertEquals(2, front.length);
		assertEquals(3, front[0]);
		assertEquals(2, front[1]);
		Object o = p1.pull();
		assertEquals(3, o);
		// Pulling from the source does not re-call compute
		assertEquals(2, sq1.getComputeCount());
		assertEquals(1, sq2.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(0, oq1.size());
		assertEquals(0, fronts.size());
		// Calling hasNext again should return false
		assertFalse(p1.hasNext());
		assertEquals(0, iq1.size());
		assertEquals(0, iq2.size());
		// Both input queues are empty, as upstream pulls are only called
		// if all pullables have events to be consumed
	}

	@Test
	public void testQueuesBinaryPullStutter()
	{
		Object[] front;
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		spw.setStutterAmount(2);
		StutteringQueueSource sq1 = new StutteringQueueSource();
		sq1.setStutterAmount(1);
		sq1.setEvents(3, 1, 4, 1, 5).loop(false);
		StutteringQueueSource sq2 = new StutteringQueueSource();
		sq2.setStutterAmount(1);
		sq2.setEvents(2, 7).loop(false);
		Connector.connect(sq1, 0, spw, 0);
		Connector.connect(sq2, 0, spw, 1);
		Queue<Object> iq1 = spw.getInputQueue(0);
		Queue<Object> iq2 = spw.getInputQueue(1);
		Queue<Object> oq1 = spw.getOutputQueue(0);
		Queue<Object> oq2 = spw.getOutputQueue(1);
		Queue<Object[]> fronts = spw.getFronts();
		Pullable p1 = spw.getPullableOutput(0);
		Pullable p2 = spw.getPullableOutput(1);
		assertEquals(0, iq1.size());
		assertEquals(0, iq2.size());
		assertEquals(0, oq1.size());
		assertEquals(0, oq2.size());
		assertEquals(0, fronts.size());
		assertTrue(p1.hasNext());
		// Asking hasNext to the source required one call to compute on sq1
		assertEquals(1, sq1.getComputeCount());
		// Asking hasNext to the source required one call to compute on sq2
		assertEquals(1, sq2.getComputeCount());
		// The call to compute put two events in each of the output queues
		assertEquals(0, iq1.size());
		assertEquals(0, iq2.size());
		assertEquals(2, oq1.size());
		assertEquals(3, oq1.peek());
		assertEquals(2, oq2.size());
		assertEquals(2, oq2.peek());
		assertEquals(1, fronts.size());
		front = fronts.remove();
		assertEquals(2, front.length);
		assertEquals(3, front[0]);
		assertEquals(2, front[1]);
		Object o = p1.pull();
		assertEquals(3, o);
		// Pulling from the source does not re-call compute
		assertEquals(1, sq1.getComputeCount());
		assertEquals(1, sq2.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(1, oq1.size());
		assertEquals(2, oq2.size());
		assertEquals(0, fronts.size());
		// Calling hasNext on p1 does not result in any upstream call,
		// as some output events are ready to be consumed
		assertTrue(p1.hasNext());
		assertEquals(1, sq1.getComputeCount());
		assertEquals(1, sq2.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(1, oq1.size());
		assertEquals(2, oq2.size());
		assertEquals(0, fronts.size());
		o = p1.pull();
		assertEquals(3, o);
		assertEquals(1, sq1.getComputeCount());
		assertEquals(1, sq2.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(0, oq1.size());
		assertEquals(2, oq2.size());
		assertEquals(0, fronts.size());
		// Ditto for p2
		assertTrue(p2.hasNext());
		assertEquals(1, sq1.getComputeCount());
		assertEquals(1, sq2.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(0, oq1.size());
		assertEquals(2, oq2.size());
		assertEquals(0, fronts.size());
		o = p2.pull();
		assertEquals(2, o);
		assertEquals(1, sq1.getComputeCount());
		assertEquals(1, sq2.getComputeCount());
		assertEquals(0, iq1.size());
		assertEquals(0, oq1.size());
		assertEquals(1, oq2.size());
		assertEquals(0, fronts.size());
	}

	/**
	 * Checks the behavior of a synchronous processor, with an input arity
	 * greater than one, in push mode.
	 * <ul>
	 * <li>Events are buffered in their respective input queues if no complete
	 * front can be processed</li>
	 * <li>A call to {@link Pushable#push(Object)} that completes an event front
	 * results immediately in exactly one call to
	 * {@link SingleProcessor#compute(Object[], Queue)}, which in turn produces exactly
	 * one output front at a time</li>
	 * <li>When this happens, one event is removed from each input queue</li>
	 * <li>The events processed by the <i>i</i>-th call to
	 * {@link SingleProcessor#compute(Object[], Queue)}
	 * are exactly the event front produced by the <i>i</i>-th call to
	 * {@link Pushable#push(Object)} on each <tt>Pushable</tt></li> 
	 * </ul>
	 */
	@Test
	public void testQueuesBinaryPush()
	{
		Object[] front;
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		BlackHole bh = new BlackHole(2);
		Connector.connect(spw, bh);
		Queue<Object[]> fronts = spw.getFronts();
		Queue<Object> iq1 = spw.getInputQueue(0);
		Queue<Object> iq2 = spw.getInputQueue(1);
		Queue<Object> oq1 = spw.getOutputQueue(0);
		Queue<Object> oq2 = spw.getOutputQueue(1);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		assertEquals(2, spw.getInputArity());
		assertEquals(2, spw.getOutputArity());
		assertTrue(iq1.isEmpty());
		assertTrue(iq2.isEmpty());
		assertTrue(oq1.isEmpty());
		assertTrue(oq2.isEmpty());
		p1.push(0);
		assertEquals(1, iq1.size());
		assertEquals(0, iq2.size());
		assertEquals(0, oq1.size());
		assertEquals(0, oq2.size());
		assertEquals(0, fronts.size());
		p1.push(1);
		assertEquals(2, iq1.size());
		assertEquals(0, iq2.size());
		assertEquals(0, oq1.size());
		assertEquals(0, oq2.size());
		assertEquals(0, fronts.size());
		p2.push(20);
		assertEquals(1, iq1.size());
		assertEquals(0, iq2.size());
		assertEquals(0, oq1.size());
		assertEquals(0, oq2.size());
		assertEquals(1, fronts.size());
		front = fronts.remove();
		assertEquals(2, front.length);
		assertEquals(0, front[0]);
		assertEquals(20, front[1]);
		p2.push(30);
		assertEquals(0, iq1.size());
		assertEquals(0, iq2.size());
		assertEquals(0, oq1.size());
		assertEquals(0, oq2.size());
		assertEquals(1, fronts.size());
		front = fronts.remove();
		assertEquals(2, front.length);
		assertEquals(1, front[0]);
		assertEquals(30, front[1]);
		p2.push(40);
		assertEquals(0, iq1.size());
		assertEquals(1, iq2.size());
		assertEquals(0, oq1.size());
		assertEquals(0, oq2.size());
		assertEquals(0, fronts.size());
	}

	@Test
	public void testQueuesDuplicateStatePush1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		BlackHole bh = new BlackHole(2);
		Connector.connect(spw, bh);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p1.push(10);
		TestableSingleProcessor spw2 = spw.duplicate(true);
		assertEquals(1, spw2.getInputQueue(0).size());
		assertEquals(0, spw2.getInputQueue(1).size());
		assertEquals(0, spw2.getOutputQueue(0).size());
		assertEquals(0, spw2.getOutputQueue(1).size());
		assertEquals(10, spw2.getInputQueue(0).peek());
	}

	@Test
	public void testQueuesDuplicateStatePush2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		BlackHole bh = new BlackHole(2);
		Connector.connect(spw, bh);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p2.push(10);
		TestableSingleProcessor spw2 = spw.duplicate(true);
		assertEquals(0, spw2.getInputQueue(0).size());
		assertEquals(1, spw2.getInputQueue(1).size());
		assertEquals(0, spw2.getOutputQueue(0).size());
		assertEquals(0, spw2.getOutputQueue(1).size());
		assertEquals(10, spw2.getInputQueue(1).peek());
	}

	@Test
	public void testQueuesDuplicateNoStatePush1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		BlackHole bh = new BlackHole(2);
		Connector.connect(spw, bh);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p1.push(10);
		TestableSingleProcessor spw2 = spw.duplicate(false);
		assertEquals(0, spw2.getInputQueue(0).size());
		assertEquals(0, spw2.getInputQueue(1).size());
		assertEquals(0, spw2.getOutputQueue(0).size());
		assertEquals(0, spw2.getOutputQueue(1).size());
	}

	@Test
	public void testQueuesDuplicateNoStatePush2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		BlackHole bh = new BlackHole(2);
		Connector.connect(spw, bh);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p2.push(10);
		TestableSingleProcessor spw2 = spw.duplicate(false);
		assertEquals(0, spw2.getInputQueue(0).size());
		assertEquals(0, spw2.getInputQueue(1).size());
		assertEquals(0, spw2.getOutputQueue(0).size());
		assertEquals(0, spw2.getOutputQueue(1).size());
	}

	/**
	 * Checks that calling {@link Pushable#end()} on a <tt>Pushable</tt> pushes
	 * the events created by an unary processor's {@link SingleProcessor#onEnd(Queue)},
	 * if any. Additional calls to {@link Pushable#end()} have no effect on the
	 * processor.
	 */
	@Test
	public void testEndPush1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		SinkLast bh = new SinkLast();
		Connector.connect(spw, bh);
		Pushable p1 = spw.getPushableInput();
		p1.push(0);
		assertEquals(0, bh.getLast());
		assertEquals(0, spw.getCallsToEnd());
		p1.end();
		assertEquals(999, bh.getLast());
		assertEquals(1, spw.getCallsToEnd());
		p1.end();
		assertEquals(1, spw.getCallsToEnd());
	}

	/**
	 * Checks that calling {@link Pushable#end()} on the first <tt>Pushable</tt> pushes
	 * the events created by a binary processor's {@link SingleProcessor#onEnd(Queue)},
	 * if any. Additional calls to {@link Pushable#end()} have no effect on the
	 * processor.
	 */
	@Test
	public void testEndPush2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		SinkLast bh1 = new SinkLast();
		SinkLast bh2 = new SinkLast();
		Connector.connect(spw, 0, bh1, 0);
		Connector.connect(spw, 1, bh2, 0);
		assertEquals(0, spw.getCallsToEnd());
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p1.end();
		// No event is waiting in p1's queue, so no new front will ever be produced
		assertEquals(1, spw.getCallsToEnd());
		assertEquals(999, bh1.getLast());
		p2.end();
		assertEquals(1, spw.getCallsToEnd());
		p1.end();
		assertEquals(1, spw.getCallsToEnd());
		p1.end();
		assertEquals(1, spw.getCallsToEnd());
	}

	/**
	 * Checks that calling {@link Pushable#end()} on the second <tt>Pushable</tt> pushes
	 * the events created by a binary processor's {@link SingleProcessor#onEnd(Queue)},
	 * if any. Additional calls to {@link Pushable#end()} have no effect on the
	 * processor.
	 */
	@Test
	public void testEndPush3()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		SinkLast bh1 = new SinkLast();
		SinkLast bh2 = new SinkLast();
		Connector.connect(spw, 0, bh1, 0);
		Connector.connect(spw, 1, bh2, 0);
		assertEquals(0, spw.getCallsToEnd());
		Pushable p1 = spw.getPushableInput(1);
		p1.end();
		assertEquals(1, spw.getCallsToEnd());
		assertEquals(999, bh1.getLast());
		p1.end();
		assertEquals(1, spw.getCallsToEnd());
		p1.end();
		assertEquals(1, spw.getCallsToEnd());
	}
	
	/**
	 * Checks that calling {@link Pushable#end()} on the second <tt>Pushable</tt> pushes
	 * the events created by a binary processor's {@link SingleProcessor#onEnd(Queue)},
	 * if any. Additional calls to {@link Pushable#end()} have no effect on the
	 * processor.
	 */
	@Test
	public void testEndPush4()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		SinkLast bh1 = new SinkLast();
		SinkLast bh2 = new SinkLast();
		Connector.connect(spw, 0, bh1, 0);
		Connector.connect(spw, 1, bh2, 0);
		assertEquals(0, spw.getCallsToEnd());
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p1.push(10);
		p1.push(15);
		p1.end();
		assertEquals(0, spw.getCallsToEnd()); // Not yet
		assertNull(bh1.getLast());
		p1.end();
		assertEquals(0, spw.getCallsToEnd()); // Still not yet
		p2.push(3);
		assertEquals(10, bh1.getLast());
		assertEquals(3, bh2.getLast());
		p2.end();
		assertEquals(1, spw.getCallsToEnd());
		assertEquals(999, bh1.getLast());
		assertEquals(999, bh2.getLast());
	}
	
	/**
	 * Checks that calling {@link Pushable#end()} on the second <tt>Pushable</tt> pushes
	 * the events created by a binary processor's {@link SingleProcessor#onEnd(Queue)},
	 * if any. Additional calls to {@link Pushable#end()} have no effect on the
	 * processor.
	 */
	@Test
	public void testEndPush5()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		QueueSink bh1 = new QueueSink(2);
		Connector.connect(spw, 0, bh1, 0);
		Connector.connect(spw, 1, bh1, 1);
		Queue<Object[]> final_q = bh1.getQueue();
		Object[] front;
		assertEquals(0, spw.getCallsToEnd());
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p1.push(10);
		p1.push(15);
		p1.end();
		assertEquals(0, spw.getCallsToEnd()); // Not yet
		assertTrue(final_q.isEmpty());
		p1.end();
		assertEquals(0, spw.getCallsToEnd()); // Still not yet
		p2.push(3);
		assertEquals(0, spw.getCallsToEnd());
		front = final_q.remove();
		assertEquals(10, front[0]);
		assertEquals(3, front[1]);
		p2.push(4);
		assertEquals(1, spw.getCallsToEnd());
		front = final_q.remove();
		assertEquals(15, front[0]);
		assertEquals(4, front[1]);
		front = final_q.remove();
		assertEquals(999, front[0]);
		assertEquals(999, front[1]);
		p2.push(5);
		assertEquals(1, spw.getCallsToEnd());
		assertTrue(final_q.isEmpty());
	}
	
	/**
	 * Checks that a <tt>false</tt> return value to {@link SingleProcessor#compute(Object[], Queue)}
	 * triggers {@link Pushable#end()} on the processor's downstream output
	 * pushables, but <em>not</em> {@link SingleProcessor#onEnd(Queue)} on the
	 * processor itself. (Binary version)
	 */
	@Test
	public void testEndPush6()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		TestableSingleProcessor spw_d1 = new TestableSingleProcessor(1, 1);
		BlackHole bh1 = new BlackHole();
		TestableSingleProcessor spw_d2 = new TestableSingleProcessor(1, 1);
		BlackHole bh2 = new BlackHole();
		Connector.connect(spw, 0, spw_d1, 0);
		Connector.connect(spw, 1, spw_d2, 0);
		Connector.connect(spw_d1, bh1);
		Connector.connect(spw_d2, bh2);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		spw.m_computeReturn = false;
		p1.push(0);
		assertEquals(0, spw_d1.getCallsToEnd());
		assertEquals(0, spw_d2.getCallsToEnd());
		p2.push(0);
		assertEquals(1, spw_d1.getCallsToEnd());
		assertEquals(1, spw_d2.getCallsToEnd());
		assertEquals(0, spw.getCallsToEnd());
	}
	
	/**
	 * Checks that a <tt>false</tt> return value to {@link SingleProcessor#compute(Object[], Queue)}
	 * triggers {@link Pushable#end()} on the processor's downstream output
	 * pushables, but <em>not</em> {@link SingleProcessor#onEnd(Queue)} on the
	 * processor itself. (Unary version)
	 */
	@Test
	public void testEndPush7()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_d1 = new TestableSingleProcessor(1, 1);
		BlackHole bh1 = new BlackHole();
		Connector.connect(spw, 0, spw_d1, 0);
		Connector.connect(spw_d1, bh1);
		Pushable p1 = spw.getPushableInput(0);
		spw.m_computeReturn = false;
		p1.push(0);
		assertEquals(1, spw_d1.getCallsToEnd());
		assertEquals(0, spw.getCallsToEnd());
	}

	@Test
	public void testResetPush1()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		BlackHole bh = new BlackHole(2);
		Connector.connect(spw, bh);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p1.push(10);
		assertEquals(1, spw.getInputQueue(0).size());
		assertEquals(0, spw.getInputQueue(1).size());
		assertEquals(0, spw.getOutputQueue(0).size());
		assertEquals(0, spw.getOutputQueue(1).size());
		spw.reset();
		assertEquals(0, spw.getInputQueue(0).size());
		assertEquals(0, spw.getInputQueue(1).size());
		assertEquals(0, spw.getOutputQueue(0).size());
		assertEquals(0, spw.getOutputQueue(1).size());
	}

	@Test
	public void testResetPush2()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		BlackHole bh = new BlackHole(2);
		Connector.connect(spw, bh);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p2.push(10);
		assertEquals(0, spw.getInputQueue(0).size());
		assertEquals(1, spw.getInputQueue(1).size());
		assertEquals(0, spw.getOutputQueue(0).size());
		assertEquals(0, spw.getOutputQueue(1).size());
		spw.reset();
		assertEquals(0, spw.getInputQueue(0).size());
		assertEquals(0, spw.getInputQueue(1).size());
		assertEquals(0, spw.getOutputQueue(0).size());
		assertEquals(0, spw.getOutputQueue(1).size());
	}
	
	/**
	 * Checks that once the processor's {@link SingleProcessor#compute(Object[], Queue)}
	 * method is called and returns <tt>false</tt>, it is never called again.
	 * Moreover, further calls to {@link Pushable#push(Object)} do not accumulate
	 * events in the input queue.
	 */
	@Test
	public void testHasMorePush()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		BlackHole bh1 = new BlackHole();
		BlackHole bh2 = new BlackHole();
		Connector.connect(spw, 0, bh1, 0);
		Connector.connect(spw, 1, bh2, 0);
		Pushable p1 = spw.getPushableInput(0);
		Pushable p2 = spw.getPushableInput(1);
		p1.push(0);
		p2.push(1);
		p1.push(2);
		assertEquals(1, spw.getFronts().size());
		assertEquals(1, spw.getInputQueue(0).size());
		spw.m_computeReturn = false;
		p1.push(3);
		p2.push(4);
		assertEquals(2, spw.getFronts().size());
		assertTrue(spw.getInputQueue(0).isEmpty());
		assertTrue(spw.getInputQueue(1).isEmpty());
		p1.push(4);
		p1.push(5);
		p2.push(6);
		assertEquals(2, spw.getFronts().size());
		assertTrue(spw.getInputQueue(0).isEmpty());
		assertTrue(spw.getInputQueue(1).isEmpty());
	}
	
	/**
	 * Checks that once the processor's {@link SingleProcessor#compute(Object[], Queue)}
	 * method is called and returns <tt>false</tt>, it is never called again.
	 * Moreover, further calls to {@link Pushable#pull(Object)} do not fetch
	 * events from upstream.
	 */
	@Test
	public void testHasMorePull()
	{
		StutteringQueueSource qs1 = new StutteringQueueSource();
		qs1.setEvents(3, 1, 4);
		qs1.setStutterAmount(2);
		StutteringQueueSource qs2 = new StutteringQueueSource();
		qs2.setEvents(2, 7, 1);
		qs2.setStutterAmount(1);
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		Connector.connect(qs1, 0, spw, 0);
		Connector.connect(qs2, 0, spw, 1);
		Pullable p1 = spw.getPullableOutput(0);
		Pullable p2 = spw.getPullableOutput(1);
		p1.pull();
		assertEquals(1, spw.getFronts().size());
		spw.m_computeReturn = false;
		p1.pull();
		assertEquals(2, spw.getFronts().size());
		try
		{
			p1.pull();
		}
		catch (ProcessorException e)
		{
			// Should throw an exception, as no more event is available
		}
		assertEquals(2, spw.getFronts().size());
	}
	
	/**
	 * Dummy test on start. Since {@link SingleProcessor} does not implement
	 * anything in this method, this is just to ensure the empty code is
	 * covered.
	 */
	@Test
	public void testStart()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		spw.start();
	}
	
	/**
	 * Dummy test on start. Since {@link SingleProcessor} does not implement
	 * anything in this method, this is just to ensure the empty code is
	 * covered.
	 */
	@Test
	public void testStop()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		spw.stop();
	}
	
	/**
	 * Checks that the input and output queues are serialized as a map
	 * with the proper keys.
	 * @throws PrintException
	 */
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint1() throws PrintException
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		spw.getInputQueue(0).add("foo");
		spw.getInputQueue(1).add(11);
		spw.getOutputQueue(0).add(22);
		spw.getOutputQueue(1).add("bar");
		spw.setState("baz");
		spw.setContext("123", "456");
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Map<String,Object> map = (Map<String,Object>) iop.print(spw);
		assertEquals(5, map.size());
		List<Queue<Object>> in_q = (List<Queue<Object>>) map.get(SingleProcessor.s_inputQueuesKey);
		assertEquals(2, in_q.size());
		assertEquals(1, in_q.get(0).size());
		assertEquals("foo", in_q.get(0).peek());
		assertEquals(1, in_q.get(1).size());
		assertEquals(11, in_q.get(1).peek());
		List<Queue<Object>> out_q = (List<Queue<Object>>) map.get(SingleProcessor.s_outputQueuesKey);
		assertEquals(2, out_q.size());
		assertEquals(1, out_q.get(0).size());
		assertEquals(22, out_q.get(0).peek());
		assertEquals(1, out_q.get(1).size());
		assertEquals("bar", out_q.get(1).peek());
		assertEquals("baz", map.get(SingleProcessor.s_contentsKey));
		Context c = (Context) map.get(SingleProcessor.s_contextKey);
		assertEquals(1, c.size());
		assertEquals("456", c.get("123"));
		ProcessorQueryable pc = (ProcessorQueryable) map.get(SingleProcessor.s_queryableKey);
		assertNotNull(pc);
	}
	
	@Test
	public void testRead() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		Context context = new Context();
		context.put("123", "456");
		map.put(SingleProcessor.s_contextKey, context);
		List<Queue<Object>> in_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("foo" + i);
			in_q.add(q);
		}
		map.put(SingleProcessor.s_inputQueuesKey, in_q);
		List<Queue<Object>> out_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("bar" + i);
			out_q.add(q);
		}
		map.put(SingleProcessor.s_outputQueuesKey, out_q);
		map.put(SingleProcessor.s_contentsKey, "baz");
		map.put(SingleProcessor.s_queryableKey, new ProcessorQueryable("procfoo", 1, 1));
		IdentityObjectReader ior = new IdentityObjectReader();
		TestableSingleProcessor spw = (TestableSingleProcessor) new TestableSingleProcessor(0, 0).read(ior, map);
		assertNotNull(spw);
		assertEquals(1, spw.getInputQueue(0).size());
		assertEquals("foo0", spw.getInputQueue(0).peek());
		assertEquals(1, spw.getInputQueue(1).size());
		assertEquals("foo1", spw.getInputQueue(1).peek());
		assertEquals(1, spw.getOutputQueue(0).size());
		assertEquals("bar0", spw.getOutputQueue(0).peek());
		assertEquals(1, spw.getOutputQueue(1).size());
		assertEquals("bar1", spw.getOutputQueue(1).peek());
		assertEquals("baz", spw.getState());
		assertEquals("456", spw.getContext("123"));
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid1() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(SingleProcessor.s_contextKey, new Context());
		List<Integer> in_q = new ArrayList<Integer>(2);
		for (int i = 0; i < 2; i++)
		{
			in_q.add(i);
		}
		map.put(SingleProcessor.s_inputQueuesKey, in_q);
		List<Queue<Object>> out_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("bar" + i);
			out_q.add(q);
		}
		map.put(SingleProcessor.s_outputQueuesKey, out_q);
		map.put(SingleProcessor.s_contentsKey, "baz");
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid2() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(SingleProcessor.s_contextKey, new Context());
		List<Queue<Object>> in_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("foo" + i);
			in_q.add(q);
		}
		map.put(SingleProcessor.s_inputQueuesKey, in_q);
		List<Integer> out_q = new ArrayList<Integer>(2);
		for (int i = 0; i < 2; i++)
		{
			out_q.add(i);
		}
		map.put(SingleProcessor.s_outputQueuesKey, out_q);
		map.put(SingleProcessor.s_contentsKey, "baz");
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid3() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(SingleProcessor.s_contextKey, new Context());
		map.put(SingleProcessor.s_inputQueuesKey, 0);
		List<Queue<Object>> out_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("bar" + i);
			out_q.add(q);
		}
		map.put(SingleProcessor.s_outputQueuesKey, out_q);
		map.put(SingleProcessor.s_contentsKey, "baz");
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid4() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(SingleProcessor.s_contextKey, new Context());
		List<Queue<Object>> in_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("foo" + i);
			in_q.add(q);
		}
		map.put(SingleProcessor.s_inputQueuesKey, in_q);
		map.put(SingleProcessor.s_outputQueuesKey, 0);
		map.put(SingleProcessor.s_contentsKey, "baz");
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid5() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(SingleProcessor.s_contextKey, new Context());
		List<Queue<Object>> out_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("bar" + i);
			out_q.add(q);
		}
		map.put(SingleProcessor.s_outputQueuesKey, out_q);
		map.put(SingleProcessor.s_contentsKey, "baz");
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid6() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		List<Queue<Object>> in_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("foo" + i);
			in_q.add(q);
		}
		map.put(SingleProcessor.s_inputQueuesKey, in_q);
		map.put(SingleProcessor.s_contentsKey, "baz");
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid7() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		List<Queue<Object>> in_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("foo" + i);
			in_q.add(q);
		}
		map.put(SingleProcessor.s_inputQueuesKey, in_q);
		List<Queue<Object>> out_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("bar" + i);
			out_q.add(q);
		}
		map.put(SingleProcessor.s_outputQueuesKey, out_q);
		map.put(SingleProcessor.s_contentsKey, "baz");
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, map);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid8() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, 0);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid9() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		Context context = new Context();
		context.put("123", "456");
		map.put(SingleProcessor.s_contextKey, context);
		List<Queue<Object>> in_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("foo" + i);
			in_q.add(q);
		}
		map.put(SingleProcessor.s_inputQueuesKey, in_q);
		List<Queue<Object>> out_q = new ArrayList<Queue<Object>>(2);
		for (int i = 0; i < 2; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			q.add("bar" + i);
			out_q.add(q);
		}
		map.put(SingleProcessor.s_outputQueuesKey, out_q);
		map.put(SingleProcessor.s_contentsKey, "baz");
		IdentityObjectReader ior = new IdentityObjectReader();
		new TestableSingleProcessor(0, 0).read(ior, map);
	}
	
	@SuppressWarnings("deprecation")
	@Test
	public void testHasNextSoftUnary()
	{
		QueueSource qs = new QueueSource().setEvents(1, 2).loop(false);
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Connector.connect(qs, spw);
		Pullable p = spw.getPullableOutput();
		assertEquals(NextStatus.YES, p.hasNextSoft());
		assertEquals(1, p.pullSoft());
		assertEquals(NextStatus.YES, p.hasNextSoft());
		assertEquals(2, p.pullSoft());
		assertEquals(NextStatus.NO, p.hasNextSoft());
	}
	
	@SuppressWarnings("deprecation")
	@Test
	public void testHasNextSoftBinary()
	{
		QueueSource qs1 = new QueueSource().setEvents(1, 2).loop(false);
		QueueSource qs2 = new QueueSource().setEvents(4, 8).loop(false);
		TestableSingleProcessor spw = new TestableSingleProcessor(2, 2);
		Connector.connect(qs1, 0, spw, 0);
		Connector.connect(qs2, 0, spw, 1);
		Pullable p1 = spw.getPullableOutput(0);
		Pullable p2 = spw.getPullableOutput(1);
		assertEquals(NextStatus.YES, p1.hasNextSoft());
		assertEquals(1, p1.pullSoft());
		assertEquals(NextStatus.YES, p2.hasNextSoft());
		assertEquals(4, p2.pullSoft());
		assertEquals(NextStatus.YES, p2.hasNextSoft());
		assertEquals(8, p2.pullSoft());
		assertEquals(NextStatus.NO, p2.hasNextSoft());
	}
	
	/**
	 * Checks that a processor queryable has the same input/output arity
	 * as the underlying processor, is not null, and that multiple calls
	 * to the queryable return the same object.
	 */
	@Test
	public void testQueryable()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		ProcessorQueryable pq2 = (ProcessorQueryable) spw.getQueryable();
		assertEquals(pq, pq2);
	}
	
	/**
	 * Checks that calling {@link Processor#reset()} on a processor resets its
	 * internal queryable to a new object.
	 */
	@Test
	public void testQueryableReset()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		assertNotNull(pq);
		assertEquals(1, pq.getInputArity());
		assertEquals(1, pq.getOutputArity());
		spw.reset();
		ProcessorQueryable pq2 = (ProcessorQueryable) spw.getQueryable();
		assertFalse(pq == pq2);
	}
	
	@Test
	public void testQueryableConnectedUpstream()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_up = new TestableSingleProcessor(1, 1);
		Connector.connect(spw_up, spw);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		ProcessorQueryable pq_up = (ProcessorQueryable) spw_up.getQueryable();
		assertEquals(spw_up.getQueryable(), pq.getInputConnection(0).m_queryable);
		assertEquals(spw.getQueryable(), pq_up.getOutputConnection(0).m_queryable);
	}
	
	@Test
	public void testQueryableConnectedDownstream()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw_dn = new TestableSingleProcessor(1, 1);
		Connector.connect(spw, spw_dn);
		ProcessorQueryable pq = (ProcessorQueryable) spw.getQueryable();
		ProcessorQueryable pq_dn = (ProcessorQueryable) spw_dn.getQueryable();
		assertEquals(spw_dn.getQueryable(), pq.getOutputConnection(0).m_queryable);
		assertEquals(spw.getQueryable(), pq_dn.getInputConnection(0).m_queryable);
	}
	
	public static Map<String,Object> getPrintedMap(int in_arity, int out_arity, Object queryable, Object contents)
	{
		Map<String,Object> map = new HashMap<String,Object>();
		Context context = new Context();
		map.put(SingleProcessor.s_contextKey, context);
		List<Queue<Object>> in_q = new ArrayList<Queue<Object>>(in_arity);
		for (int i = 0; i < in_arity; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			in_q.add(q);
		}
		map.put(SingleProcessor.s_inputQueuesKey, in_q);
		List<Queue<Object>> out_q = new ArrayList<Queue<Object>>(in_arity);
		for (int i = 0; i < out_arity; i++)
		{
			Queue<Object> q = new ArrayDeque<Object>();
			out_q.add(q);
		}
		map.put(SingleProcessor.s_outputQueuesKey, out_q);
		if (contents != null)
		{
			map.put(SingleProcessor.s_contentsKey, contents);
		}
		map.put(SingleProcessor.s_queryableKey, queryable);
		return map;
	}
}
