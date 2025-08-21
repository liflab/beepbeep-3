/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2022 Sylvain Hallé

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
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Stateful;
import ca.uqac.lif.cep.SynchronousProcessor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.util.Maps.MathMap;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

/**
 * Separates an input trace into different "slices". The slicer takes as input a
 * processor <i>p</i> and a slicing function <i>f</i>. There exists potentially
 * one instance of <i>p</i> for each value in the image of <i>f</i>.
 * <p>
 * When an event <i>e</i> arrives, the slicer evaluates <i>c</i> =
 * <i>f</i>(<i>e</i>). This value determines to what instance of <i>p</i> the
 * event will be dispatched. If no slice with such value currently exists, a new
 * instance of <i>p</i> will be created. 
 * <p>
 * What is done with the output events of each slice depends on the concrete
 * instance of {@link AbstractSlice} that is being used:
 * <ul>
 * <li>{@link Slice} outputs a map where keys are slice IDs, and values are
 * the last event produced in that slice</li>
 * <li>{@link SliceLast} outputs a collection of each event produced by each slice
 * immediately
 * </ul>
 * <p>
 * The function <i>f</i> may return {@code null}, or the special object
 * {@link ToAllSlices}. This indicates that no new slice must be created, but
 * that the incoming event must be dispatched to <em>all</em> slices one by one.
 * 
 * @author Sylvain Hallé
 * @since 0.10.2
 */
@SuppressWarnings("squid:S2160")
public abstract class AbstractSlice extends SynchronousProcessor implements Stateful
{
  /**
   * The slicing function
   */
  protected Function m_slicingFunction;

  /**
   * The internal processor
   */
  protected Processor m_processor;

  /**
   * The cleaning function
   */
  protected Function m_cleaningFunction = null;

  /**
   * A map associating slice IDs to the instance of processor associated to them
   */
  protected HashMap<Object, Processor> m_slices;

  /**
   * A map associating slice IDs to the sink that receives the events from
   * their corresponding processor
   */
  protected HashMap<Object, QueueSink> m_sinks;
  
  /**
   * A map associating slice IDs to the event positions in the input stream that
   * have been given to each slice's processor
   */
  protected HashMap<Object, List<Integer>> m_sliceIndices;
  
  /**
   * If the slicing function returns a collection, treat each element of the
   * collection as a slice id.
   */
  protected boolean m_explodeArrays = false;
  
  /**
   * Creates a dummy abstract slice. This constructor is only used for
   * deserialization purposes.
   */
  protected AbstractSlice()
  {
    super(1, 1);
  }

  
  /**
   * Creates a new AbstractSlice processor.
   * 
   * @param func
   *          The slicing function
   * @param proc
   *          The processor to apply on each slice
   * @param clean_func
   *          The cleaning function
   */
  public AbstractSlice(/* @ non_null @ */ Function func, /* @ non_null @ */ Processor proc,
      Function clean_func)
  {
    super(proc.getInputArity(), proc.getOutputArity());
    m_processor = proc;
    m_slicingFunction = func;
    m_cleaningFunction = clean_func;
    m_slices = new HashMap<Object, Processor>();
    m_sinks = new HashMap<Object, QueueSink>();
    m_sliceIndices = new HashMap<Object, List<Integer>>();
  }
  
  /**
   * Sets the processor that will be executed on each slice.
   * 
   * @param p
   *          The processor
   * @return This slicer
   */
  public AbstractSlice setProcessor(Processor p)
  {
    m_processor = p;
    return this;
  }
  
  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
  	//System.out.println(inputs[0]);
    int output_arity = getOutputArity();
    Object[] f_value = new Object[1];
    try
    {
      m_slicingFunction.evaluate(inputs, f_value);
    }
    catch (FunctionException e)
    {
      throw new ProcessorException(e);
    }
    Object slice_ids = f_value[0];
    if (slice_ids == null)
    {
      // This event applies to no slice; don't bother processing it
      return produceReturn(outputs);
    }
    Object[] slice_vals;
    if (m_explodeArrays)
    {
      if (slice_ids.getClass().isArray())
      {
        slice_vals = (Object[]) slice_ids;
      }
      if (slice_ids instanceof Collection)
      {
        Collection<?> col = (Collection<?>) slice_ids;
        slice_vals = new Object[col.size()];
        int i = 0;
        for (Object o : col)
        {
          slice_vals[i] = o;
          i++;
        }
      }
      else
      {
        slice_vals = new Object[] { slice_ids };
      }
    }
    else
    {
      slice_vals = new Object[] { slice_ids };
    }
    for (Object slice_id : slice_vals)
    {
      Set<Object> slices_to_process = new HashSet<Object>();
      if (slice_id instanceof ToAllSlices || slice_id == null)
      {
        slices_to_process.addAll(m_slices.keySet());
      }
      else
      {
        if (!m_slices.containsKey(slice_id))
        {
          // First time we see this value: create new slice
          Processor p = m_processor.duplicate();
          m_slices.put(slice_id, p);
          addContextFromSlice(p, slice_id);
          QueueSink sink = new QueueSink(output_arity);
          Connector.connect(p, sink);
          m_sinks.put(slice_id, sink);
          if (m_eventTracker != null)
          {
            //p.setEventTracker(m_eventTracker.getCopy(false));
            m_sliceIndices.put(slice_id, new ArrayList<Integer>());
          }
        }
        slices_to_process.add(slice_id);
      }
      for (Object s_id : slices_to_process)
      {
        // Find processor corresponding to that slice
        Processor slice_p = m_slices.get(s_id);
        // If this slice hasn't been cleaned up...
        if (slice_p != null)
        {
          QueueSink sink_p = m_sinks.get(s_id);
          if (m_eventTracker != null)
          {
            m_sliceIndices.get(s_id).add(m_inputCount);
          }
          // Push the input into the processor
          for (int i = 0; i < inputs.length; i++)
          {
            Object o_i = inputs[i];
            Pushable p = slice_p.getPushableInput(i);
            p.push(o_i);
          }
          // Collect the output from that processor
          Object[] out = sink_p.remove();
          // Can we clean that slice?
          Object[] can_clean = new Object[1];
          if (m_cleaningFunction != null)
          {
            try
            {
              m_cleaningFunction.evaluate(out, can_clean);
            }
            catch (FunctionException e)
            {
              throw new ProcessorException(e);
            }
          }
          if (can_clean != null && can_clean.length > 0 && can_clean[0] instanceof Boolean
              && (Boolean) (can_clean[0]))
          {
            // Yes: remove the processor for that slice
            m_slices.remove(s_id);
            m_sinks.remove(s_id);
          }
          handleNewSliceValue(s_id, out[0], outputs);
        }
      }
    }
    m_inputCount++;
    return produceReturn(outputs);
  }

  /**
   * Sets whether a slice function that returns a collection of values must be
   * handled as individual slice IDs.
   * 
   * @param b
   *          Set to {@code true} to handle collections as multiple IDs. The
   *          default is {@code false}
   * @return This slicer
   */
  public AbstractSlice explodeCollections(boolean b)
  {
    m_explodeArrays = b;
    return this;
  }

  /**
   * Adds elements to the context of a newly created slice. By default, nothing is
   * done. Descendants of this class may want to add context elements to the
   * processor, based on the value of the newly created slice.
   * 
   * @param p
   *          The newly created processor
   * @param slice
   *          The value associated to the slice
   */
  public void addContextFromSlice(Processor p, Object slice)
  {
    // By default, do nothing
  }

  @Override
  public void reset()
  {
    super.reset();
    m_slices.clear();
    m_slicingFunction.reset();
    if (m_cleaningFunction != null)
    {
      m_cleaningFunction.reset();
    }
  }

  /**
   * Gets the number of slices the slicer currently handles
   * 
   * @return The number of slices
   */
  public int getActiveSliceCount()
  {
    return m_slices.size();
  }
  
  /**
   * Copies the content of the current abstract slice processor into another
   * instance.
   * @param as The other instance of abstract slice
   * @param with_state Whether the duplication is stateful or not
   * @since 0.10.6
   */
  protected void copyInto(AbstractSlice as, boolean with_state)
  {
  	// We do not duplicate cleaning function as it is taken care of by the children's constructor
  	as.m_explodeArrays = m_explodeArrays;
  	as.m_processor = m_processor.duplicate(with_state);
  	as.m_slicingFunction = m_slicingFunction.duplicate(with_state);
    as.setContext(m_context);
    for (Map.Entry<Object,Processor> e : m_slices.entrySet())
    {
    	Processor p_dup = e.getValue().duplicate(with_state);
    	QueueSink qs = new QueueSink();
    	Connector.connect(p_dup, qs);
    	as.m_slices.put(e.getKey(), p_dup);
    	as.m_sinks.put(e.getKey(), qs);
    }
    for (Map.Entry<Object,List<Integer>> e : m_sliceIndices.entrySet())
    {
    	List<Integer> list = new ArrayList<Integer>();
    	list.addAll(e.getValue());
    	as.m_sliceIndices.put(e.getKey(), list);
    }
  }
  
  @Override
  protected boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException
	{
  	boolean new_events = false;
		// Send the message to all slices
		for (Map.Entry<Object, Processor> e : m_slices.entrySet())
		{
			Processor p = e.getValue();
			Pushable pp = p.getPushableInput(0);
			QueueSink sink = m_sinks.get(e.getKey());
			int size_before = sink.getQueue().size();
			pp.notifyEndOfTrace();
			int size_after = sink.getQueue().size();
			if (size_after > size_before)
			{
				new_events = true;
				handleNewSliceValue(e.getKey(), sink.getQueue().peek(), outputs);
			}
		}
		if (new_events)
		{
			return produceReturn(outputs);
		}
		return false;
	}

  /**
   * Dummy object telling the slicer that an event must be sent to all slices
   */
  public static class ToAllSlices
  {
    public static final ToAllSlices instance = new ToAllSlices();

    private ToAllSlices()
    {
      super();
    }
  }
  
  /**
   * Produces a final return value for the slice processor. This method is
   * called once a new incoming event has been pushed to all the relevant slices,
   * and {@link #handleNewSliceValue(Object, Object, Queue)} has been called
   * for all slices that produced an output event. 
   * @param outputs The processor's output queue
   * @return {@code true} if the processor is expected to output new events
   * in the future, {@code false} otherwise.
   */
  protected abstract boolean produceReturn(Queue<Object[]> outputs);
  
  /**
   * Handles the situation where one of the slices produces a new event.
   * Depending on the type of slice processor, a different processing will
   * be done in this method.
   * @param slice_id The id of the slice that produced an output event
   * @param value The output event
   * @param outputs The slice processor's output queue
   */
  protected abstract void handleNewSliceValue(Object slice_id, Object value,
      Queue<Object[]> outputs);

  /**
   * @since 0.11
   */
  @Override
  public Object getState()
  {
  	MathMap<Object,InternalProcessorState> state = new MathMap<Object,InternalProcessorState>();
  	for (Map.Entry<Object,Processor> e : m_slices.entrySet())
  	{
  		state.put(e.getKey(), new InternalProcessorState(e.getValue()));	
  	}
  	return state;
  }

}
