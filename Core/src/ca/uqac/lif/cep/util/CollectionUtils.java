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
package ca.uqac.lif.cep.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.InvalidArgumentException;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.tmf.SinkLast;

/**
 * A container object for functions applying to generic collections.
 * @author Sylvain Hallé
 *
 */
public class CollectionUtils 
{
	/**
	 * Gets all the elements of the collection that satisfy some condition.
	 * This condition is specified as an unary function that is successively
	 * applied to each element of the collection; if the function returns
	 * <tt>true</tt>, the element is added to the output result, otherwise it
	 * is discarded.
	 * <p>
	 * This function preserves the type of the input. That is, if the input
	 * is a set, it will return a set; if the input is a list, it will return
	 * a list. 
	 * 
	 * @author Sylvain Hallé
	 */
	public static class GetElements extends UnaryFunction<Object,Object>
	{
		/**
		 * The condition to evaluate on each element
		 */
		protected UnaryFunction<?,Boolean> m_condition;

		protected GetElements()
		{
			super(Object.class, Object.class);
		}

		/**
		 * Gets a new instance of the function
		 * @param condition The condition to evaluate on each element
		 */
		public GetElements(UnaryFunction<?,Boolean> condition)
		{
			this();
			m_condition = condition;
		}

		/**
		 * Sets the condition to evaluate on each element
		 * @param condition The condition
		 */
		public void setCondition(UnaryFunction<Object,Boolean> condition)
		{
			m_condition = condition;
		}

		@Override
		public Object getValue(Object x) 
		{
			Collection<Object> c = null;
			if (x instanceof Set)
			{
				c = new HashSet<Object>();
			}
			else if (x instanceof List)
			{
				c = new ArrayList<Object>();
			}
			else
			{
				throw new InvalidArgumentException(this, 0);
			}
			for (Object o : (Collection<?>) x)
			{
				Object[] in = new Object[1];
				in[0] = o;
				Object[] values = new Object[1];
				m_condition.evaluate(in, values);
				if ((Boolean) values[0])
				{
					c.add(o);
				}
			}
			return c;
		}
	}

	@SuppressWarnings("rawtypes")
	public static class Contains extends BinaryFunction<Collection,Object,Boolean>
	{
		/**
		 * A single instance of this function
		 */
		public static final transient Contains instance = new Contains();

		private Contains()
		{
			super(Collection.class, Object.class, Boolean.class);
		}

		@Override
		public Boolean getValue(Collection x, Object y)
		{
			if (x == null || y == null)
			{
				return false;
			}
			return x.contains(y);
		}
	}

	/**
	 * Runs each element of a collection into a processor, and collect its
	 * output.
	 */
	public static class RunOn extends SingleProcessor
	{
		protected Processor m_processor;

		protected transient SinkLast m_sink;

		protected transient Pushable m_pushable;

		public RunOn(Processor processor)
		{
			super(1, processor.getOutputArity());
			int out_arity = processor.getOutputArity();
			m_processor = processor;
			m_pushable = m_processor.getPushableInput();
			m_sink = new SinkLast(out_arity);
			Connector.connect(m_processor, m_sink);
		}

		@Override
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) throws ProcessorException 
		{
			m_processor.reset();
			for (Object o : (Collection<?>) inputs[0])
			{
				m_pushable.push(o);
			}
			Object[] last = m_sink.getLast();
			if (last != null)
			{
				Object[] outs = new Object[last.length];
				for (int i = 0; i < last.length; i++)
				{
					outs[i] = last[i];
				}
				outputs.add(outs);
			}
			return true;
		}

		@Override
		public Processor duplicate()
		{
			return new RunOn(m_processor.duplicate());
		}
	}
}
