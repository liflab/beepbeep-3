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
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.InvalidArgumentException;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.tmf.SinkLast;

/**
 * A container object for functions and processors applying to generic
 * collections, i.e. "bags" of objects.
 * @author Sylvain Hallé
 */
public class Bags 
{
	protected Bags()
	{
		// Utility class
	}
	
	/**
	 * Checks if a set is contains another
	 */
	public static final Contains contains = new Contains();
	
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
	public static class FilterElements extends UnaryFunction<Object,Object>
	{
		/**
		 * The condition to evaluate on each element
		 */
		protected UnaryFunction<?,Boolean> m_condition;

		protected FilterElements()
		{
			super(Object.class, Object.class);
		}

		/**
		 * Gets a new instance of the function
		 * @param condition The condition to evaluate on each element
		 */
		public FilterElements(UnaryFunction<?,Boolean> condition)
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
		protected Contains()
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
		protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
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
		public RunOn duplicate()
		{
			return new RunOn(m_processor.duplicate());
		}
	}
	
	/**
	 * Converts a front of <i>n</i> input events into a collection of
	 * <i>n</i> objects. 
	 * @author Sylvain Hallé
	 */
	public abstract static class ToCollection extends Function
	{
		/**
		 * An array that keeps the types of each input stream
		 */
		protected Class<?>[] m_types;
		
		/**
		 * Creates a new ToList function
		 * @param types The types of each input stream
		 */
		public ToCollection(Class<?> ... types)
		{
			super();
			m_types = types;
		}
		
		@Override
		public int getInputArity() 
		{
			return m_types.length;
		}

		@Override
		public int getOutputArity() 
		{
			return 1;
		}

		@Override
		public void reset() 
		{
			// Nothing to do
		}

		@Override
		public void getInputTypesFor(Set<Class<?>> classes, int index)
		{
			classes.add(m_types[index]);
		}
	}
	
	/**
	 * Converts a front of <i>n</i> events into an array of
	 * <i>n</i> objects. In such a case, the list preserves the ordering
	 * of the events: element <i>i</i> corresponds to the <i>i</i>-th
	 * input stream.
	 */
	public static class ToArray extends ToCollection
	{
		public ToArray(Class<?> ... types)
		{
			super(types);
		}
		
		@Override
		public Class<?> getOutputTypeFor(int index) 
		{
			return (new Object[]{}).getClass();
		}

		@Override
		public ToArray duplicate() 
		{
			return new ToArray(m_types);
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			Object[] out = new Object[inputs.length];
			for (int i = 0; i < inputs.length; i++)
			{
				out[i] = inputs[i];
			}
			outputs[0] = out;
		}
	}
	
	/**
	 * Converts a front of <i>n</i> events into a list of
	 * <i>n</i> objects. In such a case, the list preserves the ordering
	 * of the events: element <i>i</i> corresponds to the <i>i</i>-th
	 * input stream.
	 */
	public static class ToList extends ToCollection
	{
		public ToList(Class<?> ... types)
		{
			super(types);
		}

		@Override
		public ToList duplicate() 
		{
			return new ToList(m_types);
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			List<Object> out = new ArrayList<Object>(inputs.length);
			for (int i = 0; i < inputs.length; i++)
			{
				out.add(inputs[i]);
			}
			outputs[0] = out;
		}

		@Override
		public Class<?> getOutputTypeFor(int index) 
		{
			return List.class;
		}
	}
	
	/**
	 * Converts a front of <i>n</i> events into a set of
	 * <i>n</i> objects.
	 */
	public static class ToSet extends ToCollection
	{
		public ToSet(Class<?> ... types)
		{
			super(types);
		}

		@Override
		public ToSet duplicate() 
		{
			return new ToSet(m_types);
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			Set<Object> out = new HashSet<Object>(inputs.length);
			for (int i = 0; i < inputs.length; i++)
			{
				out.add(inputs[i]);
			}
			outputs[0] = out;
		}

		@Override
		public Class<?> getOutputTypeFor(int index) 
		{
			return Set.class;
		}
	}
	
	/**
	 * Given a set/list/array, returns a <em>new</em> set/list/array whose 
	 * content is the result of applying a function to each element.
	 * 
	 * @author Sylvain Hallé
	 */
	public static class ApplyToAll extends UnaryFunction<Object,Object>
	{
		/**
		 * The function to apply on each element
		 */
		protected Function m_function;

		public ApplyToAll()
		{
			super(Object.class, Object.class);
		}

		public ApplyToAll(Function function)
		{
			this();
			m_function = function;
		}

		/**
		 * Sets the function to apply on each element
		 * @param function The condition
		 */
		public void setCondition(Function function)
		{
			m_function = function;
		}

		@Override
		public Object getValue(Object x) 
		{
			if (x instanceof List)
			{
				List<Object> out = new ArrayList<Object>(((List<?>) x).size());
				for (Object o : (List<?>) x)
				{
					Object[] in = new Object[1];
					in[0] = o;
					Object[] values = new Object[1];
					m_function.evaluate(in, values);
					out.add(values[0]);
				}
				return out;
			}
			if (x instanceof Set)
			{
				Set<Object> out = new HashSet<Object>();
				for (Object o : (Set<?>) x)
				{
					Object[] in = new Object[1];
					in[0] = o;
					Object[] values = new Object[1];
					m_function.evaluate(in, values);
					out.add(values[0]);
				}
				return out;
			}
			if (x.getClass().isArray())
			{
				Object[] in_array = (Object[]) x;
				Object[] out = new Object[in_array.length];
				for (int i = 0; i < in_array.length; i++)
				{
					Object[] in = new Object[1];
					in[0] = in_array[i];
					Object[] values = new Object[1];
					m_function.evaluate(in, values);
					out[i] = values[0];
				}
				return out;
			}
			throw new InvalidArgumentException(this, 0);
		}
	}

}
