/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2025 Sylvain Hallé

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

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Stateful;
import ca.uqac.lif.cep.UniformProcessor;
import java.util.Set;

/**
 * Applies a function to input events to produce output events. This class
 * provides a way to "lift" any <i>m</i>-to-<i>n</i> function into an
 * <i>m</i>-to-<i>n</i> processor, by simply calling the function on the inputs
 * to produce the outputs.
 * <p>
 * In earlier versions of the library, this class was called
 * {@code FunctionProcessor}.
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
   * Instantiates a new function processor
   * 
   * @param comp
   *          The computable object responsible for the computation
   */
  public ApplyFunction(Function comp)
  {
    super(comp.getInputArity(), comp.getOutputArity());
    m_function = comp;
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
      m_function.evaluate(inputs, outputs, m_context);
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

	@Override
	public Object getState()
	{
		return null;
	}
}
