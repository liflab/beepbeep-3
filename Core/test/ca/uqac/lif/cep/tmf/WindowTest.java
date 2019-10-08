package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.*;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.SingleProcessorTestTemplate;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.cep.TestUtilities.TestableSingleProcessor;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.SlidableFunction;
import ca.uqac.lif.cep.tmf.Window.CircularBuffer;
import ca.uqac.lif.cep.tmf.Window.ProcessorWindow;
import ca.uqac.lif.cep.tmf.Window.GenericWindow;
import ca.uqac.lif.cep.tmf.Window.SlidableWindow;
import ca.uqac.lif.cep.util.Numbers;

public class WindowTest
{
	@Test
	public void testMultiplePushable1()
	{
		SingleProcessorTestTemplate.checkMultiplePushable1(new Window(new Passthrough(), 2));
	}
	
	@Test
	public void testMultiplePullable1()
	{
		SingleProcessorTestTemplate.checkMultiplePullable1(new Window(new Passthrough(), 2));
	}

	@Test
	public void testArityGeneric()
	{
		SingleProcessorTestTemplate.checkArity(new Window(new Passthrough(), 2), 1, 1);
	}
	
	@Test
	public void testArityFunction()
	{
		SingleProcessorTestTemplate.checkArity(new Window(new Numbers.Average(), 2), 1, 1);
	}
	
	@Test
	public void testOutputProcessor()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Window win = new Window(spw, 3);
		assertEquals(3, win.getWidth());
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
	
	@Test
	public void testResetProcessor()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Window win = new Window(spw, 3);
		assertEquals(3, win.getWidth());
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
		win.reset();
		assertEquals(1, spw.getCallsToReset());
	}
	
	@Test
	public void testDuplicateProcessorState()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Window win = new Window(spw, 3);
		BlackHole bh = new BlackHole();
		Connector.connect(win, bh);
		Pushable p = win.getPushableInput();
		p.push("foo");
		p.push("bar");
		Window win_dup = win.duplicate(true);
		assertFalse(win == win_dup);
		assertFalse(win.m_windowProcessor == win_dup.m_windowProcessor);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Window win = new Window(spw, 3);
		Map<String,Object> printed = (Map<String,Object>) iop.print(win);
		ProcessorWindow pw = (ProcessorWindow) printed.get(SingleProcessor.s_contentsKey);
		assertEquals(3, pw.m_windowWidth);
		assertEquals(spw, pw.m_processor);
	}
	
	@Test
	public void testSlidableWindowOutput()
	{
		TestableSlidableFunction tsf = new TestableSlidableFunction();
		SlidableWindow sw = new SlidableWindow(tsf, 3);
		assertEquals(3, sw.getWidth());
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();
		sw.compute(new Object[] {3}, out_queue, null);
		assertEquals(1, tsf.getCallsToEvaluate());
		assertEquals(0, tsf.getCallsToDevaluate());
		assertEquals(3, tsf.m_lastEvaluate);
		sw.compute(new Object[] {1}, out_queue, null);
		assertEquals(2, tsf.getCallsToEvaluate());
		assertEquals(0, tsf.getCallsToDevaluate());
		assertEquals(1, tsf.m_lastEvaluate);
		sw.compute(new Object[] {4}, out_queue, null);
		assertEquals(3, tsf.getCallsToEvaluate());
		assertEquals(0, tsf.getCallsToDevaluate());
		assertEquals(4, tsf.m_lastEvaluate);
		sw.compute(new Object[] {1}, out_queue, null);
		assertEquals(4, tsf.getCallsToEvaluate());
		assertEquals(1, tsf.getCallsToDevaluate());
		assertEquals(1, tsf.m_lastEvaluate);
		assertEquals(3, tsf.m_lastDevaluate);
		sw.compute(new Object[] {5}, out_queue, null);
		assertEquals(5, tsf.getCallsToEvaluate());
		assertEquals(2, tsf.getCallsToDevaluate());
		assertEquals(5, tsf.m_lastEvaluate);
		assertEquals(1, tsf.m_lastDevaluate);
		tsf.reset();
		assertEquals(1, tsf.getCallsToReset());
	}
	
	@Test
	public void testSlidableWindowDuplicate()
	{
		TestableSlidableFunction tsf = new TestableSlidableFunction();
		SlidableWindow sw = new SlidableWindow(tsf, 3);
		assertEquals(3, sw.getWidth());
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();
		sw.compute(new Object[] {3}, out_queue, null);
		assertEquals(1, tsf.getCallsToEvaluate());
		assertEquals(0, tsf.getCallsToDevaluate());
		sw.compute(new Object[] {1}, out_queue, null);
		assertEquals(2, tsf.getCallsToEvaluate());
		assertEquals(0, tsf.getCallsToDevaluate());
		sw.compute(new Object[] {4}, out_queue, null);
		assertEquals(3, tsf.getCallsToEvaluate());
		assertEquals(0, tsf.getCallsToDevaluate());
		sw.compute(new Object[] {1}, out_queue, null);
		assertEquals(4, tsf.getCallsToEvaluate());
		assertEquals(1, tsf.getCallsToDevaluate());
		tsf.reset();
		assertEquals(1, tsf.getCallsToReset());
	}
	
	@Test
	public void testGenericWindowOutput()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Queue<Object[]> fronts = spw.getFronts();
		ProcessorWindow gw = new ProcessorWindow(spw, 3);
		assertEquals(3, gw.getWidth());
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();
		gw.compute(new Object[] {3}, out_queue, null);
		assertEquals(1, gw.m_window.m_size);
		assertEquals(0, fronts.size());
		gw.compute(new Object[] {1}, out_queue, null);
		assertEquals(2, gw.m_window.m_size);
		assertEquals(0, fronts.size());
		gw.compute(new Object[] {4}, out_queue, null);
		assertEquals(3, gw.m_window.m_size);
		assertEquals(3, fronts.size());
		assertEquals(3, fronts.remove()[0]);
		assertEquals(1, fronts.remove()[0]);
		assertEquals(4, fronts.remove()[0]);
		assertEquals(1, spw.getCallsToReset());
		gw.compute(new Object[] {1}, out_queue, null);
		assertEquals(3, gw.m_window.m_size);
		assertEquals(3, fronts.size());
		assertEquals(1, fronts.remove()[0]);
		assertEquals(4, fronts.remove()[0]);
		assertEquals(1, fronts.remove()[0]);
		assertEquals(2, spw.getCallsToReset());
	}
	
	@Test
	public void testGenericWindowReset()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Queue<Object[]> fronts = spw.getFronts();
		ProcessorWindow gw = new ProcessorWindow(spw, 3);
		assertEquals(3, gw.getWidth());
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();
		gw.compute(new Object[] {3}, out_queue, null);
		assertEquals(1, gw.m_window.m_size);
		assertEquals(0, fronts.size());
		gw.compute(new Object[] {1}, out_queue, null);
		assertEquals(2, gw.m_window.m_size);
		assertEquals(0, fronts.size());
		gw.compute(new Object[] {4}, out_queue, null);
		assertEquals(3, gw.m_window.m_size);
		assertEquals(3, fronts.size());
		assertEquals(3, fronts.remove()[0]);
		assertEquals(1, fronts.remove()[0]);
		assertEquals(4, fronts.remove()[0]);
		assertEquals(1, spw.getCallsToReset());
		gw.reset();
		assertEquals(2, spw.getCallsToReset());
		assertEquals(0, gw.m_window.m_size);
	}
	
	@Test
	public void testGenericWindowDuplicateState()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Queue<Object[]> fronts = spw.getFronts();
		ProcessorWindow gw = new ProcessorWindow(spw, 3);
		assertEquals(3, gw.m_windowWidth);
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();
		gw.compute(new Object[] {3}, out_queue, null);
		assertEquals(1, gw.m_window.m_size);
		assertEquals(0, fronts.size());
		ProcessorWindow gw_dup = gw.duplicate(true);
		assertFalse(gw == gw_dup);
		assertFalse(gw.m_processor == gw_dup.m_processor);
		assertFalse(gw.m_window == gw_dup.m_window);
		assertEquals(gw.m_windowWidth, gw_dup.m_windowWidth);
		assertEquals(gw.m_window.m_size, gw_dup.m_window.m_size);
	}
	
	@Test
	public void testGenericWindowDuplicateNoState()
	{
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		Queue<Object[]> fronts = spw.getFronts();
		ProcessorWindow gw = new ProcessorWindow(spw, 3);
		assertEquals(3, gw.m_windowWidth);
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();
		gw.compute(new Object[] {3}, out_queue, null);
		assertEquals(1, gw.m_window.m_size);
		assertEquals(0, fronts.size());
		ProcessorWindow gw_dup = gw.duplicate();
		assertFalse(gw == gw_dup);
		assertFalse(gw.m_processor == gw_dup.m_processor);
		assertFalse(gw.m_window == gw_dup.m_window);
		assertEquals(gw.m_windowWidth, gw_dup.m_windowWidth);
		assertEquals(0, gw_dup.m_window.m_size);
	}
	
	@Test
	public void testCircularBuffer1()
	{
		Object out;
		CircularBuffer<Integer> cb = new CircularBuffer<Integer>(3);
		assertEquals(0, cb.m_size);
		assertFalse(cb.isFull());
		out = cb.add(3);
		assertEquals(1, cb.m_size);
		assertFalse(cb.isFull());
		assertNull(out);
		out = cb.add(1);
		assertEquals(2, cb.m_size);
		assertFalse(cb.isFull());
		assertNull(out);
		out = cb.add(4);
		assertEquals(3, cb.m_size);
		assertTrue(cb.isFull());
		assertNull(out);
		out = cb.add(1);
		assertEquals(3, cb.m_size);
		assertTrue(cb.isFull());
		assertEquals(3, out);
		out = cb.add(5);
		assertEquals(3, cb.m_size);
		assertTrue(cb.isFull());
		assertEquals(1, out);
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
	
	@Test
	public void testCircularBufferDuplicateState()
	{
		CircularBuffer<Integer> cb = new CircularBuffer<Integer>(3);
		cb.add(3);
		cb.add(1);
		CircularBuffer<Integer> cb_dup = cb.duplicate(true);
		assertFalse(cb == cb_dup);
		assertEquals(cb.m_head, cb_dup.m_head);
		assertEquals(cb.m_size, cb_dup.m_size);
		assertFalse(cb.m_buffer == cb_dup.m_buffer);
		assertEquals(cb.m_buffer.length, cb_dup.m_buffer.length);
		assertEquals(cb.m_buffer[0], cb_dup.m_buffer[0]);
		assertEquals(cb.m_buffer[1], cb_dup.m_buffer[1]);
		assertEquals(cb.m_buffer[2], cb_dup.m_buffer[2]);
	}
	
	@Test
	public void testCircularBufferDuplicateNoState()
	{
		CircularBuffer<Integer> cb = new CircularBuffer<Integer>(3);
		cb.add(3);
		cb.add(1);
		CircularBuffer<Integer> cb_dup = cb.duplicate();
		assertFalse(cb == cb_dup);
		assertEquals(0, cb_dup.m_head);
		assertEquals(0, cb_dup.m_size);
		assertFalse(cb.m_buffer == cb_dup.m_buffer);
		assertEquals(cb.m_buffer.length, cb_dup.m_buffer.length);
	}
	
	/**
	 * A {@link SlidableFunction} with additional methods to query its internal
	 * state, for testing purposes.
	 */
	public static class TestableSlidableFunction implements SlidableFunction
	{
		protected List<Object> m_buffer;
		
		protected int m_callsToEvaluate = 0;
		
		protected int m_callsToDevaluate = 0;
		
		protected int m_callsToReset = 0;
		
		protected Object m_lastEvaluate;
		
		protected Object m_lastDevaluate;
		
		public TestableSlidableFunction()
		{
			super();
			m_buffer = new ArrayList<Object>();
		}

		@Override
		public int getInputArity() 
		{
			return 1;
		}

		@Override
		public int getOutputArity() 
		{
			return 1;
		}
		
		public int getCallsToEvaluate()
		{
			return m_callsToEvaluate;
		}
		
		public int getCallsToDevaluate()
		{
			return m_callsToDevaluate;
		}
		
		public int getCallsToReset()
		{
			return m_callsToReset;
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			m_buffer.add(inputs[0]);
			m_callsToEvaluate++;
			m_lastEvaluate = inputs[0];
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_buffer.add(inputs[0]);
			m_callsToEvaluate++;
			m_lastEvaluate = inputs[0];
		}

		@Override
		public void reset() 
		{
			m_buffer.clear();
			m_callsToReset++;
			m_lastEvaluate = null;
			m_lastDevaluate = null;
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException
		{
			return m_buffer;
		}

		@SuppressWarnings("unchecked")
		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException 
		{
			TestableSlidableFunction tsf = new TestableSlidableFunction();
			tsf.m_buffer = (List<Object>) reader.read(o);
			return tsf;
		}

		@Override
		public TestableSlidableFunction duplicate(boolean with_state)
		{
			TestableSlidableFunction tsf = new TestableSlidableFunction();
			if (with_state)
			{
				tsf.m_buffer.addAll(m_buffer);
			}
			return tsf;
		}

		@Override
		public TestableSlidableFunction duplicate() 
		{
			return duplicate(false);
		}

		@Override
		public void devaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_lastDevaluate = inputs[0];
			m_callsToDevaluate++;
		}

		@Override
		public void devaluate(Object[] inputs, Object[] outputs) 
		{
			m_lastDevaluate = inputs[0];
			m_callsToDevaluate++;
		}
	}
}
