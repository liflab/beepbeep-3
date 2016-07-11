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

import static org.junit.Assert.assertFalse;

import java.util.Queue;
import java.util.Set;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.epl.QueueSink;

/**
 * Unit tests for the {@link Connector} class
 * @author Sylvain Hallé
 */
public class ConnectorTest 
{
	@Test
	public void testTwoUnary() throws ConnectorException
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
	public void testTwoBinary() throws ConnectorException
	{
		Passthrough p1 = new Passthrough(2);
		QueueSink qs1 = new QueueSink(2);
		Connector.connect(p1, qs1, 0, 1);
		Connector.connect(p1, qs1, 1, 0);
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
	public void testThreeUnary1() throws ConnectorException
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
	public void testThreeUnary2() throws ConnectorException
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
	public void testIncompatibleTypes() throws ConnectorException
	{
		Processor apples = new Apples();
		Processor oranges = new Oranges();
		assertFalse(Connector.isCompatible(apples, oranges, 0, 0));
	}
	
	public static class Incrementer extends FunctionProcessor
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
		public Integer evaluate(Integer x) 
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
		protected Queue<Object[]> compute(Object[] inputs) 
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Processor clone() 
		{
			// TODO Auto-generated method stub
			return null;
		}
		
		@Override
		public void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
		{
			classes.add(Number.class);
		}
		
		@Override
		public Class<?> getOutputTypeFor(int index)
		{
			return Number.class;
		}
	}
	
	public static class Oranges extends SingleProcessor
	{
		public Oranges()
		{
			super(1, 1);
		}

		@Override
		protected Queue<Object[]> compute(Object[] inputs) 
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Processor clone() 
		{
			// TODO Auto-generated method stub
			return null;
		}
		
		@Override
		public void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
		{
			classes.add(String.class);
		}
		
		@Override
		public Class<?> getOutputTypeFor(int index)
		{
			return String.class;
		}
	}
}
