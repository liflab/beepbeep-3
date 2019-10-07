package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.*;

import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.SingleProcessorTestTemplate;
import ca.uqac.lif.cep.SingleProcessorTestTemplate.IdentityObjectPrinter;
import ca.uqac.lif.cep.SingleProcessorTestTemplate.IdentityObjectReader;
import ca.uqac.lif.cep.SingleProcessorTestTemplate.SingleProcessorWrapper;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.tmf.Window.CircularBuffer;
import ca.uqac.lif.cep.tmf.Window.GenericWindow;
import ca.uqac.lif.cep.tmf.Window.ProcessorWindow;
import ca.uqac.lif.cep.util.Numbers;

public class WindowTest
{
	@Test
	public void testMultiplePushable1()
	{
		SingleProcessorTestTemplate.testMultiplePushable1(new Window(new Passthrough(), 2));
	}
	
	@Test
	public void testMultiplePullable1()
	{
		SingleProcessorTestTemplate.testMultiplePullable1(new Window(new Passthrough(), 2));
	}

	@Test
	public void tesArityGeneric()
	{
		SingleProcessorTestTemplate.testArity(new Window(new Passthrough(), 2), 1, 1);
	}
	
	@Test
	public void tesArityFunction()
	{
		SingleProcessorTestTemplate.testArity(new Window(new Numbers.Average(), 2), 1, 1);
	}
	
	@Test
	public void testOutputProcessor()
	{
		SingleProcessorWrapper spw = new SingleProcessorWrapper(1, 1);
		Window win = new Window(spw, 3);
		QueueSink qs = new QueueSink();
		Connector.connect(win, qs);
		Queue<Object[]> queue = qs.getQueue();
		Queue<Object[]> fronts = spw.getFronts();
		Pushable p = win.getPushableInput();
		p.push(3);
		assertTrue(queue.isEmpty());
		assertEquals(0, fronts.size());
		assertEquals(0, spw.getCallsToReset());
		p.push(1);
		assertTrue(queue.isEmpty());
		assertEquals(0, fronts.size());
		assertEquals(0, spw.getCallsToReset());
		p.push(4);
		assertEquals(1, queue.size());
		assertEquals(3, fronts.size());
		assertEquals(3, fronts.remove()[0]);
		assertEquals(1, fronts.remove()[0]);
		assertEquals(4, fronts.remove()[0]);
		assertEquals(1, spw.getCallsToReset());
		p.push(1);
		assertEquals(2, queue.size());
		assertEquals(3, fronts.size());
		assertEquals(1, fronts.remove()[0]);
		assertEquals(4, fronts.remove()[0]);
		assertEquals(1, fronts.remove()[0]);
		assertEquals(2, spw.getCallsToReset());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		SingleProcessorWrapper spw = new SingleProcessorWrapper(1, 1);
		Window win = new Window(spw, 3);
		Map<String,Object> printed = (Map<String,Object>) iop.print(win);
		GenericWindow pw = (GenericWindow) printed.get(SingleProcessor.s_contentsKey);
		assertEquals(3, pw.m_windowWidth);
		assertEquals(spw, pw.m_processor);
	}
	
	@Test
	public void testCircularBuffer1()
	{
		CircularBuffer<Integer> cb = new CircularBuffer<Integer>(3);
		assertEquals(0, cb.m_size);
		assertFalse(cb.isFull());
		cb.add(3);
		assertEquals(1, cb.m_size);
		assertFalse(cb.isFull());
		cb.add(1);
		assertEquals(2, cb.m_size);
		assertFalse(cb.isFull());
		cb.add(4);
		assertEquals(3, cb.m_size);
		assertTrue(cb.isFull());
		cb.add(1);
		assertEquals(3, cb.m_size);
		assertTrue(cb.isFull());
		cb.add(5);
		assertEquals(3, cb.m_size);
		assertTrue(cb.isFull());
	}
	
	@Test
	public void testCircularBufferIterator1()
	{
		CircularBuffer<Integer> cb = new CircularBuffer<Integer>(3);
		cb.add(3);
		Iterator<Integer> it = cb.iterator();
		assertNotNull(it);
		assertTrue(it.hasNext());
		assertEquals(3, (int) it.next());
		assertFalse(it.hasNext());
	}
	
	@Test
	public void testCircularBufferIterator2()
	{
		CircularBuffer<Integer> cb = new CircularBuffer<Integer>(3);
		cb.add(3);
		cb.add(1);
		cb.add(4);
		Iterator<Integer> it = cb.iterator();
		assertNotNull(it);
		assertTrue(it.hasNext());
		assertEquals(3, (int) it.next());
		assertTrue(it.hasNext());
		assertEquals(1, (int) it.next());
		assertTrue(it.hasNext());
		assertEquals(4, (int) it.next());
		assertFalse(it.hasNext());
		cb.add(1);
		Iterator<Integer> it2 = cb.iterator();
		assertNotNull(it2);
		assertFalse(it == it2);
		assertTrue(it2.hasNext());
		assertEquals(1, (int) it2.next());
		assertTrue(it2.hasNext());
		assertEquals(4, (int) it2.next());
		assertTrue(it2.hasNext());
		assertEquals(1, (int) it2.next());
		assertFalse(it2.hasNext());		
	}
	
	@Test(expected = NoSuchElementException.class)
	public void testCircularBufferIteratorOutOfBounds()
	{
		CircularBuffer<Integer> cb = new CircularBuffer<Integer>(3);
		cb.add(3);
		Iterator<Integer> it = cb.iterator();
		assertNotNull(it);
		assertTrue(it.hasNext());
		assertEquals(3, (int) it.next());
		assertFalse(it.hasNext());
		it.next();
	}
	
	@Test(expected = UnsupportedOperationException.class)
	public void testCircularBufferIteratorRemove()
	{
		CircularBuffer<Integer> cb = new CircularBuffer<Integer>(3);
		cb.add(3);
		Iterator<Integer> it = cb.iterator();
		assertNotNull(it);
		it.remove();
	}
}
