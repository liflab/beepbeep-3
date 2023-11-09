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
package ca.uqac.lif.cep.util;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Stateful;
import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.functions.BinaryFunction;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * A container object for set functions and processors. Some functions come in
 * two flavors:
 * <ul>
 * <li>The "plain" function takes as input a set object and returns the
 * <em>same</em> object, to which a modification has been applied. Note
 * however that in this case, a call to {@link Processor#reset() reset()}
 * still results in the instantiation of a <em>new</em> set instance.</li>
 * <li>The "new" function takes as input a set object, and returns a <em>new
 * copy</em> of the object with the modification made to it.</li>
 * </ul>
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class Sets
{
  protected Sets()
  {
    // Utility class
  }
  
  /**
   * Single visible instance of the function {@link IsSubsetOrEqual}
   */
  public static final IsSubsetOrEqual isSubsetOrEqual = new IsSubsetOrEqual();

  /**
   * Single visible instance of the function {@link IsSupersetOrEqual}
   */
  public static final IsSupersetOrEqual isSupersetOrEqual = new IsSupersetOrEqual();

  /**
   * Processor that updates a set.
   * @since 0.7
   */
  protected abstract static class SetUpdateProcessor extends UniformProcessor implements Stateful
  {
    /**
     * The underlying set
     */
    protected Set<Object> m_set;

    /**
     * Create a new instance of the processor
     */
    public SetUpdateProcessor()
    {
      super(1, 1);
      m_set = new HashSet<Object>();
    }

    @Override
    public void reset()
    {
      super.reset();
      m_set = new HashSet<Object>();
    }

    @Override
    public Class<?> getOutputType(int index)
    {
      return Set.class;
    }
    
    @Override
    public Object getState()
    {
    	MathSet<Object> set = new MathSet<Object>();
    	set.addAll(m_set);
    	return set;
    }
  }

  /**
   * Updates a set.
   * @since 0.7
   */
  public static class PutInto extends SetUpdateProcessor
  {
    /**
     * Create a new instance of the processor
     */
    public PutInto()
    {
      super();
    }

    @Override
    public PutInto duplicate(boolean with_state)
    {
      PutInto pi = new PutInto();
      if (with_state)
      {
        pi.m_set.addAll(m_set);
        pi.m_inputCount = m_inputCount;
      }
      return pi;
    }

    @Override
    protected boolean compute(Object[] inputs, Object[] outputs)
    {
    	boolean added = !m_set.contains(inputs[0]);
      m_set.add(inputs[0]);
      outputs[0] = m_set;
      if (m_eventTracker != null)
      {
      	if (added)
      	{
      		m_eventTracker.associateToInput(getId(), 0, m_inputCount, 0, m_inputCount);
      	}
      	if (m_inputCount > 0)
      	{
      		m_eventTracker.associateToOutput(getId(), 0, m_inputCount - 1, 0, m_inputCount);
      	}
      }
      m_inputCount++;
      return true;
    }
  }
  
  /**
   * Calculates the successive intersection of a stream of sets.
   * @since 0.11
   */
  public static class Intersect extends SetUpdateProcessor
  {
  	/**
     * Create a new instance of the processor
     */
  	public Intersect()
  	{
  		super();
  	}

		@Override
		protected boolean compute(Object[] inputs, Object[] outputs)
		{
			if (m_inputCount == 0)
			{
				m_set.addAll((Collection<?>) inputs[0]);
			}
			else
			{
				m_set.retainAll((Collection<?>) inputs[0]);
			}
			outputs[0] = m_set;
			m_inputCount++;
			return true;
		}

		@Override
		public Processor duplicate(boolean with_state)
		{
			Intersect inter = new Intersect();
			if (with_state)
			{
				inter.m_inputCount = m_inputCount;
				inter.m_outputCount = m_outputCount;
				inter.m_set.addAll(m_set);
			}
			return inter;
		}
  	
		@Override
		public String toString()
		{
			return "Intersect";
		}
  }

  /**
   * Updates a set.
   * @since 0.7
   */
  public static class PutIntoNew extends SetUpdateProcessor
  {
    /**
     * Create a new instance of the processor
     */
    public PutIntoNew()
    {
      super();
    }

    @Override
    public PutIntoNew duplicate(boolean with_state)
    {
      PutIntoNew pi = new PutIntoNew();
      if (with_state)
      {
        pi.m_set.addAll(m_set);
      }
      return pi;
    }

    @Override
    protected boolean compute(Object[] inputs, Object[] outputs)
    {
    	boolean added = !m_set.contains(inputs[0]);
      m_set.add(inputs[0]);
      HashSet<Object> new_set = new HashSet<Object>();
      new_set.addAll(m_set);
      outputs[0] = new_set;
      if (m_eventTracker != null)
      {
      	if (added)
      	{
      		m_eventTracker.associateToInput(getId(), 0, m_inputCount, 0, m_inputCount);
      	}
      	if (m_inputCount > 0)
      	{
      		m_eventTracker.associateToOutput(getId(), 0, m_inputCount - 1, 0, m_inputCount);
      	}
      }
      m_inputCount++;
      return true;
    }
  }

  /**
   * Checks if a set is a subset of another. The first argument is the set to
   * check, and the second argument is the reference set.
   * @since 0.7
   */
  @SuppressWarnings("rawtypes")
  public static class IsSubsetOrEqual extends BinaryFunction<Set, Set, Boolean>
  {
    protected IsSubsetOrEqual()
    {
      super(Set.class, Set.class, Boolean.class);
    }

    @SuppressWarnings("unchecked")
    @Override
    public Boolean getValue(Set x, Set y)
    {
      return y.containsAll(x);
    }
  }

  /**
   * Checks if a set is a superset of another. The first argument is the set to
   * check, and the second argument is the reference set.
   * @since 0.7
   */
  @SuppressWarnings("rawtypes")
  public static class IsSupersetOrEqual extends BinaryFunction<Set, Set, Boolean>
  {
    protected IsSupersetOrEqual()
    {
      super(Set.class, Set.class, Boolean.class);
    }

    @SuppressWarnings("unchecked")
    @Override
    public Boolean getValue(Set x, Set y)
    {
      return x.containsAll(y);
    }
  }
  
  /**
   * Implementation of a set with "mathematical" equality. Two {@link MathSet}s
   * are considered equal if they have the same elements.
   *
   * @param <T> The type of the elements in the set
   */
  public static class MathSet<T> extends HashSet<T>
  {
		/**
		 * Dummy UID.
		 */
		private static final long serialVersionUID = 1L;
		
		@Override
		public int hashCode()
		{
			int h = 0;
			for (T t : this)
			{
				if (t !=  null)
				{
					h += t.hashCode();
				}
			}
			return h;
		}
  	
		@Override
		public boolean equals(Object o)
		{
			if (!(o instanceof MathSet))
			{
				return false;
			}
			MathSet<?> set = (MathSet<?>) o;
			if (set.size() != size())
			{
				return false;
			}
			for (T t : this)
			{
				if (!set.contains(t))
				{
					return false;
				}
			}
			return true;
		}
		
		@Override
		public String toString()
		{
			StringBuilder out = new StringBuilder();
			out.append("{");
			boolean first = true;
			for (T t : this)
			{
				if (first)
				{
					first = false;
				}
				else
				{
					out.append(",");
				}
				out.append(t);
			}
			out.append("}");
			return out.toString();
		}
  }
}
