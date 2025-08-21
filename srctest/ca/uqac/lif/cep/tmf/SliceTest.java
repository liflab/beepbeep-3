/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2021 Sylvain Hallé

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
package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.*;

import java.util.List;
import java.util.Map;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.PullableException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.functions.Constant;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.functions.StreamVariable;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.util.Numbers;

/**
 * Unit tests for the {@link Slice} processor.
 * @author Sylvain Hallé
 */
public class SliceTest
{
	@SuppressWarnings("unchecked")
	@Test
	public void testSlicerPush() 
	{
		Slice sli = new Slice(Numbers.isEven, new Sum());
		QueueSink qsink = new QueueSink(1);
		Connector.connect(sli,  qsink);
		Pushable in = sli.getPushableInput(0);
		Map<Object,Object> map;
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qsink.getQueue(0);
			in.push(1);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(1.0f, map.get(false));
			in.push(1);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(2.0f, map.get(false));
			in.push(6);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(2.0f, map.get(false));
			assertEquals(6.0f, map.get(true));
			in.push(2);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(2.0f, map.get(false));
			assertEquals(8.0f, map.get(true));
			in.push(3);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(5.0f, map.get(false));
			assertEquals(8.0f, map.get(true));
			sli.reset();
			qsink.reset();
		}
		assertEquals(0, in.getPosition());
		assertEquals(sli, in.getProcessor());
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testSlicerPull() 
	{
		Slice sli = new Slice(Numbers.isEven, new Sum());
		QueueSource source = new QueueSource().setEvents(1, 1, 6, 2, 3);
		Connector.connect(source, sli);
		Pullable p = sli.getPullableOutput();
		Map<Object,Object> map;
		for (int k = 0; k < 2; k++)
		{
			assertEquals(0, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(1.0f, map.get(false));
			assertEquals(1, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(1, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(6.0f, map.get(true));
			assertEquals(2, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(8.0f, map.get(true));
			assertEquals(2, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(5.0f, map.get(false));
			assertEquals(8.0f, map.get(true));
			assertEquals(2, sli.getActiveSliceCount());
			sli.reset();
			source.reset();
		}
		// These methods should not do anything
		p.start();
		p.stop();
		p.dispose();
		boolean got_exception = false;
		try
		{
			p.remove();
		}
		catch (UnsupportedOperationException e)
		{
			got_exception = true;
		}
		assertTrue(got_exception);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testSlicerDuplicate() 
	{
		Slice sli1 = new Slice(Numbers.isEven, new Sum());
		Slice sli = (Slice) sli1.duplicate();
		QueueSource source = new QueueSource().setEvents(1, 1, 6, 2, 3);
		Connector.connect(source, sli);
		Pullable p = sli.getPullableOutput();
		Map<Object,Object> map;
		for (int k = 0; k < 2; k++)
		{
			assertEquals(0, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(1.0f, map.get(false));
			assertEquals(1, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(1, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(6.0f, map.get(true));
			assertEquals(2, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(8.0f, map.get(true));
			assertEquals(2, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(5.0f, map.get(false));
			assertEquals(8.0f, map.get(true));
			assertEquals(2, sli.getActiveSliceCount());
			sli.reset();
			source.reset();
		}
		// These methods should not do anything
		p.start();
		p.stop();
		p.dispose();
		assertEquals(0, p.getPosition());
		assertEquals(sli, p.getProcessor());
		boolean got_exception = false;
		try
		{
			p.remove();
		}
		catch (UnsupportedOperationException e)
		{
			got_exception = true;
		}
		assertTrue(got_exception);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testSlicerDuplicateStateful() 
	{
		Slice sli = new Slice(Numbers.isEven, new Sum());
		QueueSource source = new QueueSource().setEvents(1, 1, 6, 2, 3);
		Connector.connect(source, sli);
		Pullable p = sli.getPullableOutput();
		Map<Object,Object> map;
		assertEquals(0, sli.getActiveSliceCount());
		map = (Map<Object,Object>) p.pull();
		assertEquals(1.0f, map.get(false));
		assertEquals(1, sli.getActiveSliceCount());
		map = (Map<Object,Object>) p.pull();
		assertEquals(2.0f, map.get(false));
		assertEquals(1, sli.getActiveSliceCount());
		map = (Map<Object,Object>) p.pull();
		assertEquals(2.0f, map.get(false));
		assertEquals(6.0f, map.get(true));
		assertEquals(2, sli.getActiveSliceCount());
		map = (Map<Object,Object>) p.pull();
		assertEquals(2.0f, map.get(false));
		assertEquals(8.0f, map.get(true));
		assertEquals(2, sli.getActiveSliceCount());
		map = (Map<Object,Object>) p.pull();
		assertEquals(5.0f, map.get(false));
		assertEquals(8.0f, map.get(true));
		assertEquals(2, sli.getActiveSliceCount());
		Slice sli2 = (Slice) sli.duplicate(true);
		QueueSource source2 = new QueueSource().setEvents(0, 3, 1, 4);
		Connector.connect(source2, sli2);
		Pullable p2 = sli2.getPullableOutput();
		map = (Map<Object,Object>) p2.pull();
		assertEquals(5.0f, map.get(false));
		assertEquals(8.0f, map.get(true));
		assertEquals(2, sli.getActiveSliceCount());
		map = (Map<Object,Object>) p2.pull();
		assertEquals(8.0f, map.get(false));
		assertEquals(8.0f, map.get(true));
		assertEquals(2, sli.getActiveSliceCount());
		// Check that the original slice is not impacted
		map = (Map<Object,Object>) p.pull();
		assertEquals(6.0f, map.get(false));
		assertEquals(8.0f, map.get(true));
		assertEquals(2, sli.getActiveSliceCount());
		map = (Map<Object,Object>) p.pull();
		assertEquals(7.0f, map.get(false));
		assertEquals(8.0f, map.get(true));
		assertEquals(2, sli.getActiveSliceCount());
		// These methods should not do anything
		p.start();
		p.stop();
		p.dispose();
		assertEquals(0, p2.getPosition());
		assertEquals(sli2, p2.getProcessor());
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testSlicerAll()
	{
		Slice sli = new Slice(EvenAll.instance, new Sum());
		QueueSink qsink = new QueueSink(1);
		Connector.connect(sli,  qsink);
		Pushable in = sli.getPushableInput(0);
		Map<Object,Object> map;
		Queue<Object> queue = qsink.getQueue(0);
		in.push(1);
		map = (Map<Object,Object>) queue.poll();
		assertTrue(map.isEmpty());
		in.push(3);
		map = (Map<Object,Object>) queue.poll();
		assertEquals(3.0f, map.get(false));
		in.push(6);
		map = (Map<Object,Object>) queue.poll();
		assertEquals(3.0f, map.get(false));
		assertEquals(6.0f, map.get(true));
		in.push(2);
		map = (Map<Object,Object>) queue.poll();
		assertEquals(5.0f, map.get(false));
		assertEquals(8.0f, map.get(true));
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testSlicerClean() 
	{
		Slice sli = new Slice(Numbers.isEven, new Sum(), new FunctionTree(Numbers.isGreaterThan, StreamVariable.X, new Constant(2)));
		QueueSource source = new QueueSource().setEvents(1, 1, 2, 2, 3);
		Connector.connect(source, sli);
		Pullable p = sli.getPullableOutput();
		Map<Object,Object> map;
		for (int k = 0; k < 2; k++)
		{
			assertEquals(0, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(1.0f, map.get(false));
			assertEquals(1, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(1, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(2.0f, map.get(true));
			assertEquals(2, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(2.0f, map.get(false));
			assertEquals(4.0f, map.get(true));
			assertEquals(1, sli.getActiveSliceCount());
			map = (Map<Object,Object>) p.pull();
			assertEquals(5.0f, map.get(false));
			assertEquals(4.0f, map.get(true));
			assertEquals(0, sli.getActiveSliceCount());
			sli.reset();
			source.reset();
		}
		// These methods should not do anything
		p.start();
		p.stop();
		p.dispose();
		boolean got_exception = false;
		try
		{
			p.remove();
		}
		catch (UnsupportedOperationException e)
		{
			got_exception = true;
		}
		assertTrue(got_exception);
	}

	@Test(expected=PullableException.class)
	public void testSlicerException() 
	{
		Slice sli = new Slice(ThrowException.instance, new Sum());
		QueueSource source = new QueueSource().setEvents(1, 1, 2, 2, 3);
		Connector.connect(source, sli);
		Pullable p = sli.getPullableOutput();
		p.pull();
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testSliceLastPush()
	{
		SliceLast sl = new SliceLast(EvenAll.instance, new Passthrough());
		QueueSink sink = new QueueSink();
		Connector.connect(sl, sink);
		Queue<Object> q = sink.getQueue();
		Pushable p = sl.getPushableInput();
		p.push(3);
		List<Object> ol = (List<Object>) q.remove();
		assertEquals(1, ol.size());
		q.clear();
		p.push(1);
		assertNull(q.poll());
		p.push(6);
		ol = (List<Object>) q.remove();
		assertEquals(1, ol.size());
		q.clear();
		p.push(2);
		ol = (List<Object>) q.remove();
		assertEquals(2, ol.size());
	}

	public static class Sum extends Cumulate
	{
		public Sum()
		{
			super(new CumulativeFunction<Number>(Numbers.addition));
		}
	}

	/**
	 * Slicing function designed specifically for testing the behaviour
	 * of the slice processors. Given an integer <i>x</i>, it returns
	 * {@link ToAllSlices} if <i>x</i> is equal to 2, {@code null} if <i>x</i>
	 * is equal to 1, and {@code true} or {@code false} for the remaining
	 * numbers, depending on whether they are even or odd.  
	 */
	public static class EvenAll extends UnaryFunction<Number,Object>
	{
		public static final EvenAll instance = new EvenAll();

		protected EvenAll()
		{
			super(Number.class, Object.class);
		}

		@Override
		public Object getValue(Number x) 
		{
			if (x.intValue() == 2)
			{
				return Slice.ToAllSlices.instance;
			}
			if (x.intValue() == 1)
			{
				return null;
			}
			return x.intValue() % 2 == 0;
		}

		@Override
		public EvenAll duplicate(boolean with_state)
		{
			return instance;
		}
	}

	public static class ThrowException extends UnaryFunction<Number,Object>
	{
		public static final ThrowException instance = new ThrowException();

		protected ThrowException()
		{
			super(Number.class, Object.class);
		}

		@Override
		public Object getValue(Number x) 
		{
			throw new FunctionException("foo");
		}
	}
}
