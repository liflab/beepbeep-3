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
package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.functions.Function;

import java.util.HashMap;
import java.util.Map;
import java.util.Queue;

/**
 * Concrete version of {@link AbstractSlice} whose output is an associative
 * map between slice IDs and the last event produced by that slice processor.
 * 
 * @author Sylvain Hallé
 * @since 0.3
 */
@SuppressWarnings("squid:S2160")
public class Slice extends AbstractSlice
{
  /**
   * The last value output by the processor for each slice
   */
  protected HashMap<Object, Object> m_lastValues;

  /**
   * Creates a dummy slice processor. This constructor is only used for
   * deserialization purposes.
   */
  protected Slice()
  {
    super();
  }

  /**
   * Creates a new Slice processor.
   * 
   * @param func The slicing function
   * @param proc The processor to apply on each slice
   * @param clean_func The cleaning function
   */
  public Slice(/*@ non_null @*/ Function func, /*@ non_null @*/ Processor proc,
      Function clean_func)
  {
    super(func, proc, clean_func);
    m_lastValues = new HashMap<Object, Object>();
  }

  /**
   * Creates a new Slice processor.
   * @param func The slicing function
   * @param proc The processor to apply on each slice
   */
  public Slice(/*@ non_null @*/ Function func, /*@ non_null @*/ Processor proc)
  {
    this(func, proc, null);
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
    contents.put("last-values", m_lastValues);
    contents.put("sinks", m_sinks);
    contents.put("slices", m_slices);
    contents.put("processor", m_processor);
    contents.put("slicing-function", m_slicingFunction);
    return contents;
  }

  /**
   * @since 0.10.2
   */
  @SuppressWarnings("unchecked")
  @Override
  public Slice readState(Object o) throws ProcessorException
  {
    Map<String,Object> contents = (HashMap<String,Object>) o;
    Function cleaning_function = (Function) contents.get("cleaning-function");
    Function slicing_function = (Function) contents.get("slicing-function");
    Processor proc = (Processor) contents.get("processor");
    Slice s = new Slice(slicing_function, proc, cleaning_function);
    s.m_lastValues = (HashMap<Object,Object>) contents.get("last-values");
    s.m_sinks = (HashMap<Object,QueueSink>) contents.get("sinks");
    s.m_slices = (HashMap<Object,Processor>) contents.get("slices");
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
  public Slice duplicate(boolean with_state)
  {
    Slice s = null;
    if (m_cleaningFunction == null)
    {
      s = new Slice(m_slicingFunction.duplicate(with_state), m_processor.duplicate(with_state));
    }
    else
    {
      s = new Slice(m_slicingFunction.duplicate(with_state), m_processor.duplicate(with_state),
          m_cleaningFunction.duplicate(with_state));
    }
    super.copyInto(s, with_state);
    if (with_state)
    {
    	s.m_lastValues.putAll(m_lastValues);
    }
    return s;
  }

  @Override
  public void reset()
  {
    super.reset();
    m_lastValues = new HashMap<Object,Object>();
  }

  @Override
  protected boolean produceReturn(Queue<Object[]> outputs)
  {
    outputs.add(new Object[] {m_lastValues});
    m_outputCount++;
    return true;
  }

  @Override
  protected void handleNewSliceValue(Object slice_id, Object value, Queue<Object[]> outputs)
  {
    if (value != null)
    {
      m_lastValues.put(slice_id, value);
    }
  }
}
