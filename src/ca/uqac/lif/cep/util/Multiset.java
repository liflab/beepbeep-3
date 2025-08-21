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

import ca.uqac.lif.cep.SynchronousProcessor;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.UnaryFunction;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

/**
 * A set where each element can be present more than once.
 * @author Sylvain Hallé
 * @since 0.9
 */
public class Multiset implements Set<Object>
{
  /**
   * A single visible instance of the {@link GetCardinalities} function
   */
  public static final transient GetCardinalities getCardinalities = new GetCardinalities();
  
  /**
   * The map used to store the relation between each element and its
   * cardinality
   */
  private final Map<Object,Integer> m_map;

  /**
   * Creates an empty multiset
   */
  public Multiset()
  {
    super();
    m_map = new HashMap<Object, Integer>();
  }
  
  /**
   * Creates a multiset from the contents of another one
   * @param m The other multiset
   */
  public Multiset(/*@ non_null @*/ Multiset m)
  {
    super();
    m_map = new HashMap<Object, Integer>();
    m_map.putAll(m.m_map);
  }

  /**
   * Performs the union of two multisets
   * @param b The multiset to add
   * @return This multiset
   */
  public Multiset addAll(Multiset b)
  {
    for (Object o : b.keySet())
    {
      if (!m_map.containsKey(o))
      {
        m_map.put(o, b.get(o));
      }
      else
      {
        int cardinality = m_map.get(o) + b.get(o);
        m_map.put(o, cardinality);
      }
    }
    return this;
  }
  
  @Override
  public boolean addAll(Collection<? extends Object> arg0) 
  {
    if (arg0 instanceof Multiset)
    {
      addAll((Multiset) arg0);
      return true;
    }
    for (Object o : arg0)
    {
      addElement(o);
    }
    return true;
  }

  /**
   * Picks one element of the multiset. This assumes you don't care
   * about what element of the multiset you get, as long as you get one.
   * @return An element of the multiset, or null if the multiset is empty
   */
  public Object getAnyElement()
  {
    Set<Object> objects = m_map.keySet();
    for (Object o : objects)
    {
      // Return the first element you pick
      return o;
    }
    return null;
  }

  /**
   * Checks if an element is contained (at least once) into this multiset
   * @param o The element
   * @return true if the element is contained at least once, false otherwise
   */
  public boolean contains(Object o)
  {
    if (!m_map.containsKey(o))
    {
      return false;
    }
    int cardinality = m_map.get(o);
    return cardinality > 0;
  }

  /**
   * Adds an element to this multiset
   * @param o The element
   * @return This multiset
   */
  public Multiset addElement(Object o)
  {
    if (!m_map.containsKey(o))
    {
      m_map.put(o, 1);
    }
    else
    {
      int cardinality = m_map.get(o);
      m_map.put(o,  cardinality + 1);
    }
    return this;
  }

  @Override
  public boolean add(Object o)
  {
    addElement(o);
    return true;
  }

  /**
   * Gets the cardinality of an element
   * @param o The element
   * @return The cardinality
   */
  public int get(Object o)
  {
    if (!m_map.containsKey(o))
    {
      return 0;
    }
    return m_map.get(o);
  }

  /**
   * Gets the (normal) set of all elements in this multiset.
   * In other words, turns this multiset into a regular set. 
   * @return The set of elements
   */
  public Set<Object> keySet()
  {
    return m_map.keySet();
  }

  /**
   * Removes an element from this multiset
   * @param o The element
   * @param times The number of times to remove this element
   * @return This multiset
   */
  public Multiset removeElement(Object o, int times)
  {
    if (m_map.containsKey(o))
    {
      int cardinality = m_map.get(o);
      if (cardinality <= times)
      {
        m_map.remove(o);
      }
      else
      {
        m_map.put(o, cardinality - times);
      }
    }
    return this;
  }

  /**
   * Gets the size of the multiset
   * @return The size
   */
  @Override
  public int size()
  {
    int size = 0;
    for (int i : m_map.values())
    {
      size += i;
    }
    return size;
  }

  @Override
  public void clear()
  {
    m_map.clear();
  }

  @Override
  public String toString()
  {
    return m_map.toString();
  }

  @Override
  public boolean containsAll(Collection<?> arg0) 
  {
    if (arg0 instanceof Multiset)
    {
      Multiset set = (Multiset) arg0;
      for (Object o : set.keySet())
      {
        if (m_map.get(o) < set.get(o))
        {
          return false;
        }
      }
      return true;
    }
    else
    {
      // Normal set
      for (Object o : arg0)
      {
        if (!contains(o))
        {
          return false;
        }
      }
      return true;
    }
  }

  @Override
  public boolean isEmpty() 
  {
    return m_map.keySet().isEmpty();
  }

  @Override
  public Iterator<Object> iterator() 
  {
    return keySet().iterator();
  }

  @Override
  public boolean remove(Object arg0) 
  {
    return remove(arg0, 1);
  }

  /**
   * Removes an element a number of times
   * @param arg0 The element
   * @param times The number of times to remove it
   * @return true if the element was removed at least once,
   *   false otherwise
   */
  public boolean remove(Object arg0, int times) 
  {
    if (!contains(arg0))
    {
      return false;
    }
    removeElement(arg0, times);
    return true;
  }

  @Override
  public boolean removeAll(Collection<?> arg0) 
  {
    boolean removed = false;
    if (arg0 instanceof Multiset)
    {
      Multiset set = (Multiset) arg0;
      for (Object o : set.keySet())
      {
        // Look out: the call must be on the LHS. Otherwise,
        // if removed == true, the call would never be evaluated.
        removed = remove(o, set.get(o)) || removed;
      }
    }
    else
    {
      // Normal collection
      for (Object o : arg0)
      {
        removed = remove(o, 1) || removed;
      }
    }
    return removed;
  }

  @Override
  public boolean retainAll(Collection<?> arg0) 
  {
    boolean changed = false;
    if (arg0 instanceof Multiset)
    {
      Multiset set = (Multiset) arg0;
      for (Object o : set.keySet())
      {
        int target_card = set.get(o);
        if (m_map.get(o) > target_card)
        {
          changed = true;
          m_map.put(o, target_card);
        }
      }
      for (Object o : m_map.keySet())
      {
        if (!set.contains(o))
        {
          m_map.remove(o);
          changed = true;
        }
      }
    }
    else
    {
      // Normal set
      for (Object o : arg0)
      {
        if (get(o) > 1)
        {
          m_map.put(o, 1);
          changed = true;
        }
      }
      for (Object o : m_map.keySet())
      {
        if (!arg0.contains(o))
        {
          m_map.remove(o);
          changed = true;
        }
      }
    }
    return changed;
  }

  @Override
  public Object[] toArray() 
  {
    return m_map.values().toArray();
  }

  @Override
  public <T> T[] toArray(T[] arg0) 
  {
    // TODO Auto-generated method stub
    return null;
  }
  
  /**
   * Given a multiset and an element, returns a new multiset with this element
   * added to it.
   * @since 0.10.3
   */
  public static class Insert extends BinaryFunction<Multiset,Object,Multiset>
  {
    public static final transient Insert instance = new Insert();
    
    protected Insert()
    {
      super(Multiset.class, Object.class, Multiset.class);
    }

    @Override
    public Multiset getValue(Multiset x, Object y)
    {
      Multiset m = new Multiset(x);
      m.add(y);
      return m;
    }
    
    @Override
    public Insert duplicate(boolean with_state)
    {
      return this;
    }
  }
  
  /**
   * Gets the cardinalities of each element in a multiset.
   * The output is a map from elements to the number of times they appear
   * in the multiset.
   * @since 0.10.3
   */
  @SuppressWarnings("rawtypes")
  public static class GetCardinalities extends UnaryFunction<Multiset,Map>
  {
    protected GetCardinalities()
    {
      super(Multiset.class, Map.class);
    }

    @Override
    public Map getValue(Multiset x)
    {
      return x.m_map;
    }
    
    @Override
    public GetCardinalities duplicate(boolean with_state)
    {
      return this;
    }
  }

  /**
   * Puts incoming events into a multiset, and returns this set.
   */
  public static class PutInto extends SynchronousProcessor
  {
    protected Multiset m_set;

    public PutInto()
    {
      super(1, 1);
      m_set = new Multiset();
    }

    @Override
    protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
    {
      m_set.add(inputs[0]);
      outputs.add(new Object[] {m_set});
      return true;
    }

    @Override
    public PutInto duplicate(boolean with_state)
    {
      PutInto pi = new PutInto();
      if (with_state)
      {
        pi.m_set.addAll(m_set);
      }
      return pi;
    }
    
    @Override
    public void reset()
    {
      super.reset();
      m_set = new Multiset();
    }
  }
}
