/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2021 Sylvain Hallé

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
package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.EventTracker;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Stateful;
import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.petitpoucet.NodeFunction;
import ca.uqac.lif.petitpoucet.ProvenanceNode;
import java.util.Set;

/**
 * Applies a function to input events to produce output events. This class
 * provides a way to "lift" any <i>m</i>-to-<i>n</i> function into an
 * <i>m</i>-to-<i>n</i> processor, by simply calling the function on the inputs
 * to produce the outputs.
 * <p>
 * In earlier versions of the library, this class was called
 * <tt>FunctionProcessor</tt>.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class ApplyFunction extends UniformProcessor implements Stateful
{
  /**
   * The object responsible for the computation
   */
  protected Function m_function;

  /**
   * A shift tracker
   * @since 0.10.3
   */
  protected ShiftTracker m_shiftTracker;

  /**
   * Instantiates a new function processor
   * 
   * @param comp
   *          The computable object responsible for the computation
   */
  public ApplyFunction(Function comp)
  {
    super(comp.getInputArity(), comp.getOutputArity());
    m_function = comp;
    m_shiftTracker = new ShiftTracker();
  }

  @Override
  public void reset()
  {
    super.reset();
    m_function.reset();
  }

  @Override
  protected boolean compute(Object[] inputs, Object[] outputs)
  {
    try
    {
      m_function.evaluate(inputs, outputs, m_context, m_shiftTracker);
      m_inputCount++;
      m_outputCount++;
    }
    catch (FunctionException e)
    {
      throw new ProcessorException(e);
    }
    return true;
  }

  @Override
  public synchronized ApplyFunction duplicate(boolean with_state)
  {
    ApplyFunction out = new ApplyFunction(m_function.duplicate(with_state));
    duplicateInto(out);
    return out;
  }

  @Override
  public final void getInputTypesFor(/*@ non_null @*/ Set<Class<?>> classes, int index)
  {
    // The type is determined by that of the underlying function
    m_function.getInputTypesFor(classes, index);
  }

  @Override
  public final synchronized Class<?> getOutputType(int index)
  {
    // The type is determined by that of the underlying function
    return m_function.getOutputTypeFor(index);
  }

  @Override
  public String toString()
  {
    return m_function.toString();
  }

  /**
   * Gets the function associated to that processor
   * 
   * @return The function
   */
  public Function getFunction()
  {
    return m_function;
  }

  public void cloneInto(ApplyFunction af, boolean with_state)
  {
    super.duplicateInto(af);
    af.m_function = m_function.duplicate(with_state);
  }

  /**
   * @since 0.10.2
   */
  @Override
  public Object printState()
  {
    return m_function;
  }

  /**
   * @since 0.10.2
   */
  @Override
  public ApplyFunction readState(Object o)
  {
    Function f = (Function) o;
    return new ApplyFunction(f);
  }

  /**
   * Simple tracker proxy that records associations from the underlying function,
   * and shifts its input/output by the current position in the input/output stream
   * @since 0.10.3
   */
  protected class ShiftTracker implements EventTracker
  {
    @Override
    public void associateTo(int id, NodeFunction f, int out_stream_index, int out_stream_pos)
    {
      if (m_eventTracker != null)
      {
        m_eventTracker.associateTo(getId(), f, out_stream_index, m_outputCount);
      }
    }

    @Override
    public void associateToInput(int id, int in_stream_index, int in_stream_pos,
        int out_stream_index, int out_stream_pos)
    {
      if (m_eventTracker != null)
      {
        m_eventTracker.associateToInput(getId(), in_stream_index, m_inputCount,
            out_stream_index, m_outputCount);
      }
    }

    @Override
    public void associateToOutput(int id, int in_stream_index, int in_stream_pos,
        int out_stream_index, int out_stream_pos)
    {
      // Nothing to do
    }

    @Override
    public ProvenanceNode getProvenanceTree(int proc_id, int stream_index, int stream_pos)
    {
      throw new Error("ShiftTracker.getProvenanceTree should not be called");
    }

    @Override
    public void setConnection(int output_proc_id, int output_stream_index, int input_proc_id,
        int input_stream_index)
    {
      // Do nothing
    }

    @Override
    public void setTo(Processor ... processors)
    {
      // Do nothing
    }

    @Override
    public EventTracker getCopy()
    {
      return new ShiftTracker();
    }

		@Override
		public void add(GroupProcessor g)
		{
			// TODO Auto-generated method stub
			
		}
  }

	@Override
	public Object getState()
	{
		return null;
	}
}
