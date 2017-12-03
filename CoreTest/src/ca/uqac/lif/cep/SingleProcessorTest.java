/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.QueueSourceBatch;

/**
 * Unit tests for the {@link SingleProcessor} class.
 */
public class SingleProcessorTest 
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
		te.getPushableInput().pushFast(0);
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
		assertEquals(NextStatus.YES, p.hasNextSoft());
		p.next();
		assertEquals(NextStatus.YES, p.hasNextSoft());
		p.next();
		assertEquals(NextStatus.NO, p.hasNextSoft());
	}
	
	public static class ThrowException extends SingleProcessor
	{
		public ThrowException()
		{
			super(1, 1);
		}

		@Override
		public ThrowException duplicate()
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
