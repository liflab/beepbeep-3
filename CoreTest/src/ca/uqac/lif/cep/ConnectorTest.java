/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

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
import java.util.Set;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Connector.IncompatibleTypesException;
import ca.uqac.lif.cep.functions.ApplyFunction;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSink;

/**
 * Unit tests for the {@link Connector} class
 * @author Sylvain Hallé
 */
public class ConnectorTest
{
	@Test
	public void testOutOfBounds1()
	{
		Apples a1 = new Apples();
		Apples a2 = new Apples();
		boolean got_exception = false;
		try
		{
			Connector.connect(a1, 10, a2, 0);
		}
		catch (ConnectorException ce)
		{
			Connector.IndexOutOfBoundsException ioobe = (Connector.IndexOutOfBoundsException) ce;
			assertNotNull(ioobe.getMessage());
			got_exception = true;
		}
		assertTrue(got_exception);
	}
	
	@Test
	public void testOutOfBounds2()
	{
		Apples a1 = new Apples();
		Apples a2 = new Apples();
		boolean got_exception = false;
		try
		{
			Connector.connect(a1, 0, a2, 10);
		}
		catch (ConnectorException ce)
		{
			Connector.IndexOutOfBoundsException ioobe = (Connector.IndexOutOfBoundsException) ce;
			assertNotNull(ioobe.getMessage());
			got_exception = true;
		}
		assertTrue(got_exception);
	}
	
	@Test
	public void testConnectWithTracker() 
	{
		Apples a1 = new Apples();
		Apples a2 = new Apples();
		ProvenanceTest.DummyTracker tracker = new ProvenanceTest.DummyTracker();
		Connector.connect(tracker, a1, a2);
		assertTrue(tracker.containsConnection(a1.getId(), 0, a2.getId(), 0));
		assertFalse(tracker.containsConnection(a2.getId(), 0, a1.getId(), 0));
	}
	
	@Test
	public void testConnectNothing() 
	{
		Apples a = new Apples();
		Connector.connect(a);
		// Nothing happens
	}
	
	@Test
	public void testIsCompatible1()
	{
		assertTrue(Connector.isCompatible(new Apples(), 0, new Apples(), 0));
	}
	
	@Test
	public void testIsCompatible2()
	{
		assertFalse(Connector.isCompatible(new Apples(), 10, new Apples(), 0));
	}
	
	@Test
	public void testIsCompatible3()
	{
		assertTrue(!Connector.s_checkForTypes || !Connector.isCompatible(new Apples(), 0, new Oranges(), 0));
	}
	
	@Test
	public void testSelfLoop()
	{
		Apples a = new Apples();
		boolean got_exception = false;
		try
		{
			Connector.connect(a, a);
		}
		catch (Connector.SelfLoopException sle)
		{
			assertNotNull(sle.getMessage());
			got_exception = true;
		}
		catch (ConnectorException e)
		{
			
		}
		assertTrue(got_exception);
	}
	
	@Test
	public void testTwoUnary() 
	{
		Passthrough p1 = new Passthrough(1);
		QueueSink qs1 = new QueueSink(1);
		Connector.connect(p1, qs1);
		Pushable push1 = p1.getPushableInput(0);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qs1.getQueue(0);
			for (int i = 0; i < 5; i++)
			{
				push1.push(i);
				Utilities.queueContains(i, queue);
			}
			p1.reset();
			qs1.reset();
		}
	}
	
	@Test
	public void testTwoBinary() 
	{
		Passthrough p1 = new Passthrough(2);
		QueueSink qs1 = new QueueSink(2);
		Connector.connect(p1, 0, qs1, 1);
		Connector.connect(p1, 1, qs1, 0);
		Pushable push1 = p1.getPushableInput(0);
		Pushable push2 = p1.getPushableInput(1);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue1 = qs1.getQueue(0);
			Queue<Object> queue2 = qs1.getQueue(1);
			for (int i = 0; i < 5; i++)
			{
				push1.push(i);
				push2.push(2 * i + 1);
				Utilities.queueContains(i, queue2);
				Utilities.queueContains(2 * i + 1, queue1);
			}
			p1.reset();
			qs1.reset();
		}
	}
	
	@Test
	public void testThreeUnary1() 
	{
		Passthrough p1 = new Passthrough(1);
		QueueSink qs1 = new QueueSink(1);
		Connector.connect(p1, qs1);
		Pushable push1 = p1.getPushableInput(0);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qs1.getQueue(0);
			for (int i = 0; i < 5; i++)
			{
				push1.push(i);
				Utilities.queueContains(i, queue);
			}
			p1.reset();
			qs1.reset();
		}
	}
	
	@Test
	public void testThreeUnary2() 
	{
		Passthrough p1 = new Passthrough(1);
		Incrementer p2 = new Incrementer(10);
		QueueSink qs1 = new QueueSink(1);
		Connector.connect(p1, p2, qs1);
		Pushable push1 = p1.getPushableInput(0);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qs1.getQueue(0);
			for (int i = 0; i < 5; i++)
			{
				push1.push(i);
				Utilities.queueContains(i + 10, queue);
			}
			p1.reset();
			qs1.reset();
		}
	}
	
	@Test
	public void testIncompatibleTypes() 
	{
		Processor apples = new Apples();
		Processor oranges = new Oranges();
		assertFalse(Connector.isCompatible(apples, 0, oranges, 0));
	}
	
	@Test
	public void testConnectIncompatible()
	{
		Processor apples = new Apples();
		Processor oranges = new Oranges();
		try
		{
			Connector.connect(apples, oranges);
		}
		catch (ConnectorException e)
		{
			IncompatibleTypesException ite = (IncompatibleTypesException) e;
			assertNotNull(ite.getMessage());
		}
	}
	
	@Test
	public void testVariantOutput()
	{
		assertTrue(Connector.isCompatible(new Variants(), 0, new Oranges(), 0));
	}
	
	@Test
	public void testVariantInput()
	{
		assertTrue(Connector.isCompatible(new Oranges(), 0, new Variants(), 0));
	}
	
	public static class Incrementer extends ApplyFunction
	{
		public Incrementer(int i)
		{
			super(new Plus(i));
		}
	}
	
	public static class Plus extends UnaryFunction<Integer,Integer>
	{
		int m_plus = 0;
		
		public Plus(int i)
		{
			super(Integer.class, Integer.class);
			m_plus = i;
		}
		
		@Override
		public Integer getValue(Integer x) 
		{
			return x + 10;
		}
		
	}
	
	public static class Apples extends SingleProcessor
	{
		public Apples()
		{
			super(1, 1);
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
		{
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public Apples duplicate() 
		{
			return new Apples();
		}
		
		@Override
		public void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
		{
			classes.add(Number.class);
		}
		
		@Override
		public Class<?> getOutputType(int index)
		{
			if (index != 0)
				throw new ArrayIndexOutOfBoundsException();
			return Number.class;
		}
	}
	
	public static class Oranges extends SingleProcessor
	{
		public boolean started = false;
		
		boolean reset = false;

		public Oranges()
		{
			super(1, 1);
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
		{
			// TODO Auto-generated method stub
			return false;
		}
		
		@Override
		public void reset()
		{
			reset = true;
		}

		@Override
		public Oranges duplicate() 
		{
			return new Oranges();
		}
		
		@Override
		public void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
		{
			classes.add(String.class);
		}
		
		@Override
		public Class<?> getOutputType(int index)
		{
			if (index != 0)
				throw new ArrayIndexOutOfBoundsException();
			return String.class;
		}
		
		@Override
		public void start()
		{
			started = true;
		}
		
		@Override
		public void stop()
		{
			started = false;
		}
	}
	
	public static class Variants extends SingleProcessor
	{
		public Variants()
		{
			super(1, 1);
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
		{
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public Variants duplicate() 
		{
			return new Variants();
		}
		
		@Override
		public Class<?> getOutputType(int index)
		{
			if (index != 0)
				throw new ArrayIndexOutOfBoundsException();
			return Connector.Variant.class;
		}
	}
}
