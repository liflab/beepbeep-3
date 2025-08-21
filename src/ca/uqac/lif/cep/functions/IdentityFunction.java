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
package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.EventTracker;
import java.util.Set;

/**
 * Function that returns its input for its output. It is illustrated
 * graphically as follows:
 * <p>
 * <img src="{@docRoot}/doc-files/functions/IdentityFunction.png" alt="IdentityFunction">
 * 
 * @author Sylvain Hallé
 * @since 0.3
 */
public final class IdentityFunction extends Function
{
  /**
   * The input arity of the function (which is also its output arity)
   */
  protected int m_inArity = 1;

  /**
   * Creates a new identity function
   * 
   * @param arity
   *          The arity of the function
   */
  public IdentityFunction(int arity)
  {
    super();
    m_inArity = arity;
  }
  
  /**
   * Creates a new identity function of arity 1.
   */
  public IdentityFunction()
  {
    this(1);
  }

  @Override
  public void evaluate(Object[] inputs, Object[] outputs, Context context, EventTracker tracker)
  {
    for (int i = 0; i < inputs.length; i++)
    {
      outputs[i] = inputs[i];
      if (tracker != null)
      {
        tracker.associateToOutput(-1, i, 0, i, 0);
      }
    }
  }

  @Override
  public void evaluate(Object[] inputs, Object[] outputs)
  {
    evaluate(inputs, outputs, null);
  }

  @Override
  public int getInputArity()
  {
    return m_inArity;
  }

  @Override
  public int getOutputArity()
  {
    return m_inArity;
  }

  @Override
  public void reset()
  {
    // Nothing to do
  }

  @Override
  public IdentityFunction duplicate(boolean with_state)
  {
    return new IdentityFunction(m_inArity);
  }

  @Override
  public void getInputTypesFor(Set<Class<?>> classes, int index)
  {
    classes.add(Variant.class);
  }

  @Override
  public Class<?> getOutputTypeFor(int index)
  {
    return Variant.class;
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Object printState()
  {
    return m_inArity;
  }

  /**
   * @since 0.10.2
   */
  @Override
  public IdentityFunction readState(Object o)
  {
    return new IdentityFunction(((Number) o).intValue());
  }
}
