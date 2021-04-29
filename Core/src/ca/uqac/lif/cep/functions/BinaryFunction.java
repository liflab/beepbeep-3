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

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.EventTracker;
import java.util.Set;

/**
 * Function of two inputs and one output.
 * 
 * @param <T>
 *          The type of the first input
 * @param <V>
 *          The type of the second input
 * @param <U>
 *          The type of the output
 * 
 * @author Sylvain Hallé
 * @since 0.3
 */
public abstract class BinaryFunction<T, V, U> extends Function
{
  /**
   * The class of the first input
   */
  private Class<T> m_inputTypeLeft;

  /**
   * The class of the second input
   */
  private Class<V> m_inputTypeRight;

  /**
   * The class of the output
   */
  private Class<U> m_outputType;

  /**
   * Creates a new instance of a binary function
   * 
   * @param t
   *          The class of the first input
   * @param v
   *          The class of the second input
   * @param u
   *          The class of the output
   */
  public BinaryFunction(Class<T> t, Class<V> v, Class<U> u)
  {
    super();
    m_inputTypeLeft = t;
    m_inputTypeRight = v;
    m_outputType = u;
  }

  @SuppressWarnings("unchecked")
  @Override
  /* @ requires inputs.length == 2 */
  public void evaluate(/* @NonNull */ Object[] inputs, Object[] outputs,
      /*@ null @*/ Context context, EventTracker tracker)
  {
    outputs[0] = getValue((T) inputs[0], (V) inputs[1]);
    if (tracker != null)
    {
      trackAssociations((T) inputs[0], (V) inputs[1], (U) outputs[0], tracker);
    }
  }

  /**
   * Evaluates the function
   * 
   * @param x
   *          The first argument
   * @param y
   *          The second argument
   * @return The return value of the function
   */
  public abstract U getValue(T x, V y);
  
  /**
   * Tracks the input/output associations for the evaluation of this function
   * @param x
   *          The first argument
   * @param y
   *          The second argument
   * @param z
   *          The return value of the function
   * @param tracker
   *          The tracker
   */
  protected void trackAssociations(T x, V y, U z, EventTracker tracker)
  {
    tracker.associateToInput(-1, 0, 0, 0, 0);
    tracker.associateToInput(-1, 1, 0, 0, 0);
  }

  @Override
  public final int getInputArity()
  {
    return 2;
  }

  @Override
  public final int getOutputArity()
  {
    return 1;
  }

  /**
   * Gets a reasonable starting value if this function is used to create a
   * {@link CumulativeFunction}. You only need to override this method if the
   * function is expected to be used in a cumulative function; otherwise returning
   * null is fine.
   * 
   * @return A start value
   */
  public U getStartValue()
  {
    return null;
  }

  @Override
  public void reset()
  {
    // Do nothing
  }

  @Override
  public BinaryFunction<T, V, U> duplicate(boolean with_state)
  {
    return this;
  }

  public final Class<T> getInputTypeLeft()
  {
    return m_inputTypeLeft;
  }

  public final Class<V> getInputTypeRight()
  {
    return m_inputTypeRight;
  }

  @Override
  public final void getInputTypesFor(/* @NotNull */ Set<Class<?>> classes, int index)
  {
    if (index == 0)
    {
      classes.add(m_inputTypeLeft);
    }
    else
    {
      classes.add(m_inputTypeRight);
    }
  }

  public final Class<U> getOutputType()
  {
    return m_outputType;
  }

  @Override
  public final Class<?> getOutputTypeFor(int index)
  {
    return m_outputType;
  }

}
