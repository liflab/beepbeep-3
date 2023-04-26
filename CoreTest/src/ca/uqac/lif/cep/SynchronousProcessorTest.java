/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2023 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Pullable.PullableException;
import ca.uqac.lif.cep.Pushable.PushableException;
import ca.uqac.lif.cep.tmf.BlackHole;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.QueueSourceBatch;

/**
 * Unit tests for the {@link SynchronousProcessor} class.
 */
public class SynchronousProcessorTest 
{
	@Test(expected=PullableException.class)
	public void testPullException1() 
	{
		QueueSource qs = new QueueSource();
		qs.setEvents(new Object[]{0});
		ThrowException te = new ThrowException();
		Connector.connect(qs, te);
		Passthrough pt = new Passthrough();
		Connector.connect(te, pt);
		pt.getPullableOutput().pull();
	}
	
	@Test(expected=PushableException.class)
	public void testPushException1() 
	{
		ThrowException te = new ThrowException();
		Passthrough pt = new Passthrough();
		Connector.connect(te, pt);
		BlackHole bh = new BlackHole();
		Connector.connect(pt, bh);
		te.getPushableInput().push(0);
	}
	
	@Test(expected=PullableException.class)
	public void testPullSoftException1() 
	{
		QueueSource qs = new QueueSource();
		qs.setEvents(new Object[]{0});
		ThrowException te = new ThrowException();
		Connector.connect(qs, te);
		Passthrough pt = new Passthrough();
		Connector.connect(te, pt);
		pt.getPullableOutput().pullSoft();
		boolean got_exception = false;
		try
		{
			pt.getPullableOutput().remove();
		}
		catch (UnsupportedOperationException e)
		{
			got_exception = true;
		}
		assertTrue(got_exception);
	}
	
	@Test(expected=PushableException.class)
	public void testPushFastException1() 
	{
		ThrowException te = new ThrowException();
		Passthrough pt = new Passthrough();
		Connector.connect(te, pt);
		BlackHole bh = new BlackHole();
		Connector.connect(pt, bh);
		te.getPushableInput().push(0);
	}
	
	@Test
	public void testSamePullable()
	{
		ThrowException pt = new ThrowException();
		Pullable p1 = pt.getPullableOutput(0);
		Pullable p2 = pt.getPullableOutput(0);
		assertTrue(p1 == p2);
	}
	
	@Test
	public void testSamePushable()
	{
		ThrowException pt = new ThrowException();
		Pushable p1 = pt.getPushableInput(0);
		Pushable p2 = pt.getPushableInput(0);
		assertTrue(p1 == p2);
	}
	
	@Test
	public void testWithQueue() 
	{
		// This tests the fact that the queue inside the pullable
		// will not be empty the second time next() is called
		QueueSourceBatch qsb = new QueueSourceBatch(1);
		qsb.setEvents(new Object[]{0, 1, 2, 3});
		Passthrough pt = new Passthrough();
		Connector.connect(qsb, pt);
		Pullable p = pt.getPullableOutput();
		assertEquals(0, ((Integer) p.next()).intValue());
		assertEquals(1, ((Integer) p.next()).intValue());
		assertEquals(2, ((Integer) p.next()).intValue());
	}
	
	@Test
	public void testStop() 
	{
		QueueSource qsb = new QueueSource(1);
		qsb.setEvents(new Object[]{0, 1});
		qsb.loop(false);
		Passthrough pt = new Passthrough();
		Connector.connect(qsb, pt);
		Pullable p = pt.getPullableOutput();
		assertTrue(p.hasNext());
		p.next();
		assertTrue(p.hasNext());
		p.next();
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testStopSoft() 
	{
		QueueSource qsb = new QueueSource(1);
		qsb.setEvents(new Object[]{0, 1});
		qsb.loop(false);
		Passthrough pt = new Passthrough();
		Connector.connect(qsb, pt);
		Pullable p = pt.getPullableOutput();
		assertEquals(Pullable.NextStatus.YES, p.hasNextSoft());
		p.next();
		assertEquals(Pullable.NextStatus.YES, p.hasNextSoft());
		p.next();
		assertEquals(Pullable.NextStatus.NO, p.hasNextSoft());
	}
	
	@Test
	public void testPushFalse1()
	{
		ChooseToStop cts = new ChooseToStop();
		QueueSink sink = new QueueSink();
		Connector.connect(cts, sink);
		Pushable p = cts.getPushableInput();
		Queue<?> q = sink.getQueue();
		p.push("a");
		assertEquals(1, q.size());
		assertEquals("a", q.remove());
		cts.setState(1);
		p.push("b");
		assertEquals(1, q.size());
		assertEquals("b", q.remove());
		p.push("c");
		assertEquals(0, q.size());
	}
	
	@Test
	public void testPullFalse1()
	{
		QueueSource source =  new QueueSource().setEvents("a", "b", "c");
		ChooseToStop cts = new ChooseToStop();
		Connector.connect(source, cts);
		Pullable p = cts.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals("a", p.pull());
		cts.setState(1);
		assertTrue(p.hasNext());
		assertEquals("b", p.pull());
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testEndOfTrace1()
	{
		NotifyPassthrough np = new NotifyPassthrough();
		QueueSink sink = new QueueSink();
		Queue<?> q = sink.getQueue();
		Connector.connect(np, sink);
		Pushable p0 = np.getPushableInput(0);
		Pushable p1 = np.getPushableInput(1);
		p0.notifyEndOfTrace();
		assertEquals(0, q.size());
		p1.notifyEndOfTrace();
		assertEquals(1, q.size());
		p0.notifyEndOfTrace();
		assertEquals(1, q.size());
	}
	
	protected static class NotifyPassthrough extends SynchronousProcessor
	{

		public NotifyPassthrough()
		{
			super(2, 1);
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			return true;
		}

		@Override
		public Processor duplicate(boolean with_state)
		{
			// Don't care
			return null;
		}
		
		@Override
		protected boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException
		{
			outputs.add(new Object[] {0});
			return true;
		}
		
	}
	
	/**
	 * Processor used to test the behavior of {@link Pushable} in the case where
	 * a synchronous processor returns {@code false} on a call to
	 * {@link SynchronousProcessor#compute(Object[], Queue)}.
	 * <p>
	 * The processor has a state variable that can be set from the outside
	 * (using {@link #setState(int)} and that controls its behavior:
	 * <ul>
	 * <li>0: next call to compute will output an event and return true</li>
	 * <li>1: next call to compute will output an event and return false</li>
	 * <li>2: next call to compute will not produce an event and return false</li>
	 * </ul>
	 */
	protected static class ChooseToStop extends SynchronousProcessor
	{
		protected int m_state = 0;
		
		public ChooseToStop()
		{
			super(1, 1);
		}
		
		public void setState(int n)
		{
			m_state = n;
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			if (m_state == 2)
			{
				return false;
			}
			if (m_state == 1)
			{
				outputs.add(new Object[] {inputs[0]});
				m_state = 2;
				return false;
			}
			outputs.add(new Object[] {inputs[0]});
			return true;
		}

		@Override
		public Processor duplicate(boolean with_state)
		{
			// TODO Auto-generated method stub
			return null;
		}
		
	}
	
	public static class ThrowException extends SynchronousProcessor
	{
		public ThrowException()
		{
			super(1, 1);
		}

		@Override
		public ThrowException duplicate(boolean with_state)
		{
			return null;
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) throws ProcessorException
		{
			throw new ProcessorException("foo");
		}
	}
}
