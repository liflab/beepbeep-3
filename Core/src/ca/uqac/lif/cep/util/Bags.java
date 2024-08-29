/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2024 Sylvain Hallé

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

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.EventTracker;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SynchronousProcessor;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.InvalidArgumentException;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.tmf.SinkLast;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Queue;
import java.util.Set;

/**
 * A container object for functions and processors applying to generic
 * collections, i.e. "bags" of objects.
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class Bags
{
  protected Bags()
  {
    // Utility class
  }

  /**
   * Checks if a collection contains another
   */
  public static final Contains contains = new Contains();
  
  /**
   * Checks if an element is contained in a collection
   */
  public static final IsElement isElement = new IsElement();

  /**
   * Gets the size of a collection
   */
  public static final GetSize getSize = new GetSize();

  /**
   * Computes the Cartesian product of two collections
   */
  public static final Product product = new Product();

  /**
   * Gets any element of a bag
   */
  public static final AnyElement anyElement = new AnyElement();
  
  /**
   * Gets the maximum value of a collection
   */
  public static final MaximumValue maxValue = new MaximumValue();
  
  /**
   * Gets the minimum value of a collection
   */
  public static final MinimumValue minValue = new MinimumValue();

  /**
   * Gets all the elements of the collection that satisfy some condition. This
   * condition is specified as an unary function that is successively applied to
   * each element of the collection; if the function returns {@code true}, the
   * element is added to the output result, otherwise it is discarded.
   * <p>
   * This function preserves the type of the input. That is, if the input is a
   * set, it will return a set; if the input is a list, it will return a list.
   * 
   * @author Sylvain Hallé
   */
  public static class FilterElements extends UnaryFunction<Object, Object>
  {
    /**
     * The condition to evaluate on each element
     */
    protected Function m_condition;

    // This constructor is used for deserialization.
    protected FilterElements()
    {
      super(Object.class, Object.class);
    }

    /**
     * Gets a new instance of the function.
     * 
     * @param condition
     *          The condition to evaluate on each element. This function must
     *          be of arity 1 and return a Boolean value.
     */
    /*@ requires condition.getInputArity() == 1; @*/
    public FilterElements(Function condition)
    {
      this();
      m_condition = condition;
    }

    /**
     * Sets the condition to evaluate on each element.
     * 
     * @param condition
     *          The condition to evaluate on each element. This function must
     *          be of arity 1 and return a Boolean value.
     */
    /*@ requires condition.getInputArity() == 1; @*/
    public void setCondition(Function condition)
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

  /**
   * Checks if an object is a member of a collection.
   */
  @SuppressWarnings("rawtypes")
  public static class Contains extends BinaryFunction<Collection, Object, Boolean>
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
   * Runs each element of a collection into a processor, and collect its output.
   */
  public static class RunOn extends SynchronousProcessor
  {
    protected Processor m_processor;

    protected transient SinkLast m_sink;

    protected transient Pushable m_pushable;
    
    protected final Object[] m_default;

    /**
     * Creates a new RunOn processor
     * @param processor The processor on which to run the elements
     * of each collection
     */
    public RunOn(Processor processor)
    {
      super(1, processor.getOutputArity());
      int out_arity = processor.getOutputArity();
      m_processor = processor;
      m_pushable = m_processor.getPushableInput();
      m_sink = new SinkLast(out_arity);
      Connector.connect(m_processor, m_sink);
      m_default = null;
    }
    
    /**
     * Creates a new RunOn processor
     * @param processor The processor on which to run the elements
     * of each collection
     */
    public RunOn(Processor processor, Object[] default_values)
    {
      super(1, processor.getOutputArity());
      int out_arity = processor.getOutputArity();
      m_processor = processor;
      m_pushable = m_processor.getPushableInput();
      m_sink = new SinkLast(out_arity);
      Connector.connect(m_processor, m_sink);
      m_default = default_values;
    }

    @Override
    protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
    {
    	boolean empty_input = false;
      m_processor.reset();
      m_sink.reset();
      if (inputs[0].getClass().isArray())
      {
      	empty_input = ((Object[]) inputs[0]).length == 0;
        for (Object o : (Object[]) inputs[0])
        {
          m_pushable.push(o);
        }
      }
      else
      {
      	empty_input = ((Collection<?>) inputs[0]).size() == 0;
        for (Object o : (Collection<?>) inputs[0])
        {
          m_pushable.push(o);
        }
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
      else if (empty_input && m_default != null)
      {
      	outputs.add(m_default);
      }
      return true;
    }

    @Override
    public RunOn duplicate(boolean with_state)
    {
      return new RunOn(m_processor.duplicate(with_state), m_default);
    }
  }

  /**
   * Converts a front of <i>n</i> input events into a collection of <i>n</i>
   * objects.
   * 
   * @author Sylvain Hallé
   */
  public abstract static class ToCollection extends Function
  {
    /**
     * An array that keeps the types of each input stream
     */
    protected final Class<?>[] m_types;

    /**
     * Creates a new instance of the function by specifying the type of each
     * input argument.
     * 
     * @param types
     *          The types of each input argument
     */
    public ToCollection(Class<?> ... types)
    {
      super();
      m_types = types;
    }
    
    /**
     * Creates a new instance of the function by specifying its input arity.
     * This constructor assumes that each input argument is of type
     * {@link Variant}.
     * @param arity The input arity
     * @since 0.11
     */
    public ToCollection(int arity)
    {
    	super();
    	m_types = new Class<?>[arity];
    	for (int i = 0; i < arity; i++)
    	{
    		m_types[i] = Variant.class;
    	}
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
      super.reset();
    }

    @Override
    public void getInputTypesFor(Set<Class<?>> classes, int index)
    {
      classes.add(m_types[index]);
    }
  }

  /**
   * Converts a front of <i>n</i> events into an array of <i>n</i> objects. In
   * such a case, the list preserves the ordering of the events: element <i>i</i>
   * corresponds to the <i>i</i>-th input stream.
   */
  public static class ToArray extends ToCollection
  {
    public ToArray(Class<?> ... types)
    {
      super(types);
    }
    
    public ToArray(int arity)
    {
    	super(arity);
    }

    @Override
    public Class<?> getOutputTypeFor(int index)
    {
      return (new Object[] {}).getClass();
    }

    @Override
    public ToArray duplicate(boolean with_state)
    {
      return new ToArray(m_types);
    }

    @Override
    public void evaluate(Object[] inputs, Object[] outputs, Context context, EventTracker tracker)
    {
      Object[] out = new Object[inputs.length];
      for (int i = 0; i < inputs.length; i++)
      {
        out[i] = inputs[i];
        if (tracker != null)
        {
          tracker.associateToOutput(-1, i, 0, 0, 0);
        }
      }
      outputs[0] = out;
    }
  }

  /**
   * Converts a front of <i>n</i> events into a list of <i>n</i> objects. In such
   * a case, the list preserves the ordering of the events: element <i>i</i>
   * corresponds to the <i>i</i>-th input stream.
   */
  public static class ToList extends ToCollection
  {
    public ToList(Class<?> ... types)
    {
      super(types);
    }
    
    public ToList(int arity)
    {
    	super(arity);
    }

    @Override
    public ToList duplicate(boolean with_state)
    {
      return new ToList(m_types);
    }

    @Override
    public void evaluate(Object[] inputs, Object[] outputs, Context context, EventTracker tracker)
    {
      List<Object> out = new ArrayList<Object>(inputs.length);
      for (int i = 0; i < inputs.length; i++)
      {
        out.add(inputs[i]);
        if (tracker != null)
        {
          tracker.associateToOutput(-1, i, 0, 0, 0);
        }
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
   * Converts a front of <i>n</i> events into a set of <i>n</i> objects.
   */
  public static class ToSet extends ToCollection
  {
    public ToSet(Class<?> ... types)
    {
      super(types);
    }
    
    public ToSet(int arity)
    {
    	super(arity);
    }

    @Override
    public ToSet duplicate(boolean with_state)
    {
      return new ToSet(m_types);
    }

    @Override
    public void evaluate(Object[] inputs, Object[] outputs, Context context, EventTracker tracker)
    {
      Set<Object> out = new HashSet<Object>(inputs.length);
      for (int i = 0; i < inputs.length; i++)
      {
        out.add(inputs[i]);
        if (tracker != null)
        {
          tracker.associateToOutput(-1, i, 0, 0, 0);
        }
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
   * Gets the size of a collection
   */
  public static class GetSize extends UnaryFunction<Object, Integer>
  {
    protected GetSize()
    {
      super(Object.class, Integer.class);
    }

    @Override
    public Integer getValue(Object o)
    {
      if (o instanceof Collection)
      {
        return ((Collection<?>) o).size();
      }
      if (o.getClass().isArray())
      {
        return ((Object[]) o).length;
      }
      return 0;
    }
  }

  /**
   * Given a set/list/array, returns a <em>new</em> set/list/array whose content
   * is the result of applying a function to each element.
   * 
   * @author Sylvain Hallé
   */
  public static class ApplyToAll extends UnaryFunction<Object, Object>
  {
    /**
     * The function to apply on each element
     */
    protected Function m_function;

    // This constructor is used for deserialization.
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
     * 
     * @param function
     *          The condition
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
      if (x instanceof Collection)
      {
        Set<Object> out = new HashSet<Object>();
        for (Object o : (Collection<?>) x)
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

  /**
   * Computes the Cartesian product of two collections, returning pairs as
   * arrays.
   * 
   * @author Sylvain Hallé
   */
  @SuppressWarnings("rawtypes")
  public static class Product extends BinaryFunction<Collection, Collection, Collection>
  {
    private Product()
    {
      super(Collection.class, Collection.class, Collection.class);
    }

    @Override
    public Collection getValue(Collection x, Collection y)
    {
      Set<Object[]> out = new HashSet<Object[]>();
      for (Object o_x : x)
      {
        for (Object o_y : y)
        {
          out.add(new Object[] { o_x, o_y });
        }
      }
      return out;
    }
  }

  /**
   * Returns any element of a collection. If the collection is empty, returns
   * {@code null}.
   */
  @SuppressWarnings("rawtypes")
  public static class AnyElement extends UnaryFunction<Collection, Object>
  {
    private AnyElement()
    {
      super(Collection.class, Object.class);
    }

    @Override
    public Object getValue(Collection x)
    {
      Object o = null;
      for (Object o2 : x)
      {
        o = o2;
        break;
      }
      return o;
    }
  }

  /**
   * A 1:<i>m</i> function provided by the {@code Bags} utility class. 
   * Given a collection of size *m*, it returns as its <i>m</i> outputs 
   * the elements of the collection. It can be seen as the oppsite of 
   * {@code ToArray}, {@code ToList} and {@code ToSet}.
   * The ordering of the arguments is 
   * ensured when the input collection is itself ordered. 
   */
  public static class Explode extends Function
  {
    public Class<?>[] m_classes;

    public Explode(Class<?> ... classes)
    {
      super();
      m_classes = classes;
    }

    @Override
    public Explode duplicate(boolean with_state)
    {
      return new Explode(m_classes);
    }

    @Override
    public void evaluate(Object[] inputs, Object[] outputs, Context context, EventTracker tracker)
    {
      Object[] ins = (Object[]) inputs[0];
      for (int i = 0; i < ins.length; i++)
      {
        outputs[i] = ins[i];
        if (tracker != null)
        {
          tracker.associateToOutput(-1, 0, 0, i, 0);
        }
      }
    }

    @Override
    public int getInputArity()
    {
      return 1;
    }

    @Override
    public int getOutputArity()
    {
      return m_classes.length;
    }

    @Override
    public void getInputTypesFor(Set<Class<?>> classes, int index)
    {
      classes.add(Variant.class);
    }

    @Override
    public Class<?> getOutputTypeFor(int index)
    {
      return m_classes[index];
    }
  }

  /**
   * Converts an object into an array
   * 
   * @param o
   *          The object
   * @return An array, or {@code null} if the object could not be converted into
   *         an array.
   */
  public static Object[] toObjectArray(Object o)
  {
    if (o.getClass().isArray())
    {
      return (Object[]) o;
    }
    if (o instanceof Collection<?>)
    {
      Collection<?> c = (Collection<?>) o;
      Object[] a = new Object[c.size()];
      int i = 0;
      for (Object obj : c)
      {
        a[i++] = obj;
      }
      return a;
    }
    return null;
  }

  /**
   * Returns the element with the maximum value in a collection. If the
   * collection contains non-numerical elements, they are ignored. If
   * no numerical element is found in the collection, the function returns 0.
   * 
   * @since 0.10.2 
   */
  @SuppressWarnings("rawtypes")
  public static class MaximumValue extends UnaryFunction<Collection,Number>
  {
    protected MaximumValue()
    {
      super(Collection.class, Number.class);
    }
    
    @Override
    public Number getValue(Collection x)
    {
      if (x.isEmpty())
      {
        return 0;
      }
      boolean first = true;
      Number value = 0;
      for (Object o : x)
      {
        if (!(o instanceof Number))
        {
          continue;
        }
        Number n = (Number) o;
        if (first)
        {
          first = false;
          value = n;
        }
        else
        {
          if (value.floatValue() < n.floatValue())
          {
            value = n;
          }
        }
      }
      return value;
    }
  }
  
  /**
   * Returns the element with the maximum value in a collection. If the
   * collection contains non-numerical elements, they are ignored. If
   * no numerical element is found in the collection, the function returns 0.
   * 
   * @since 0.10.2 
   */
  @SuppressWarnings("rawtypes")
  public static class MinimumValue extends UnaryFunction<Collection,Number>
  {
    protected MinimumValue()
    {
      super(Collection.class, Number.class);
    }
    
    @Override
    public Number getValue(Collection x)
    {
      if (x.isEmpty())
      {
        return 0;
      }
      boolean first = true;
      Number value = 0;
      for (Object o : x)
      {
        if (!(o instanceof Number))
        {
          continue;
        }
        Number n = (Number) o;
        if (first)
        {
          first = false;
          value = n;
        }
        else
        {
          if (value.floatValue() > n.floatValue())
          {
            value = n;
          }
        }
      }
      return value;
    }
  }

  /**
   * Checks if an element is a member of a collection.
   * @since 0.10.2
   */
  @SuppressWarnings("rawtypes")
  public static class IsElement extends BinaryFunction<Object,Collection,Boolean>
  {
    protected IsElement()
    {
      super(Object.class, Collection.class, Boolean.class);
    }

    @Override
    public Boolean getValue(Object x, Collection y)
    {
      return y.contains(x);
    }
  }
}
