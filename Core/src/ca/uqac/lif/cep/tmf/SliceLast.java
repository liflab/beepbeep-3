/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2019 Sylvain Hallé

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

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.functions.Function;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

/**
 * Concrete version of {@link AbstractSlice} whose output is a stream of
 * lists, where each list contains all the events produced by inner slices
 * from a given input even. When multiple slices produce an output
 * event for the same input event, the order in which these events are
 * put into the list is undefined.
 * 
 * @author Sylvain Hallé
 * @since 0.10.2
 */
public class SliceLast extends AbstractSlice
{
  /**
   * A list of values produced by slice processors
   */
  protected List<Object> m_currentList;
  
  /**
   * Creates a new SliceLast processor.
   * 
   * @param func The slicing function
   * @param proc The processor to apply on each slice
   * @param clean_func The cleaning function
   */
  public SliceLast(/* @ non_null @ */ Function func, /* @ non_null @ */ Processor proc,
      Function clean_func)
  {
    super(func, proc, clean_func);
    m_currentList = new ArrayList<Object>();
  }
  
  /**
   * Creates a new SliceLast processor.
   * @param func The slicing function
   * @param proc The processor to apply on each slice
   */
  public SliceLast(/*@ non_null @*/ Function func, /*@ non_null @*/ Processor proc)
  {
    this(func, proc, null);
  }

  @Override
  protected boolean produceReturn(Queue<Object[]> outputs)
  {
    if (m_currentList.isEmpty())
    {
      return true;
    }
    ArrayList<Object> list = new ArrayList<Object>(m_currentList.size());
    list.addAll(m_currentList);
    m_currentList.clear();
    outputs.add(new Object[] {list});
    return true;
  }

  @Override
  protected void handleNewSliceValue(Object slice_id, Object value, Queue<Object[]> outputs)
  {
    if (value != null)
    {
      m_currentList.add(value);
    }
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Object printState()
  {
    Map<String,Object> contents = new HashMap<String,Object>();
    contents.put("cleaning-function", m_cleaningFunction);
    contents.put("explode-arrays", m_explodeArrays);
    contents.put("sinks", m_sinks);
    contents.put("slices", m_slices);
    contents.put("processor", m_processor);
    contents.put("list", m_currentList);
    contents.put("slicing-function", m_slicingFunction);
    return contents;
  }
  
  /**
   * @since 0.10.2
   */
  @SuppressWarnings("unchecked")
  @Override
  public SliceLast readState(Object o) throws ProcessorException
  {
    Map<String,Object> contents = (HashMap<String,Object>) o;
    Function cleaning_function = (Function) contents.get("cleaning-function");
    Function slicing_function = (Function) contents.get("slicing-function");
    Processor proc = (Processor) contents.get("processor");
    SliceLast s = new SliceLast(slicing_function, proc, cleaning_function);
    s.m_sinks = (HashMap<Object,QueueSink>) contents.get("sinks");
    s.m_slices = (HashMap<Object,Processor>) contents.get("slices");
    s.m_currentList = (List<Object>) contents.get("list");
    s.m_explodeArrays = (Boolean) contents.get("explode-arrays");
    // Connect slices to sinks
    for (Map.Entry<Object,Processor> entry : s.m_slices.entrySet())
    {
      Processor p = entry.getValue();
      if (!s.m_sinks.containsKey(entry.getKey()))
      {
        throw new ProcessorException("Cannot restore the state of the slice processor");
      }
      QueueSink qs = s.m_sinks.get(entry.getKey());
      Connector.connect(p, qs);
    }
    return s;
  }
  
  @Override
  public void reset()
  {
    super.reset();
    m_currentList.clear();
  }
}
