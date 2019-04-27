/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2018 Sylvain Hallé

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
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * A {@link Function} that raises the arity of another function.
 * Given an <i>m</i>:<i>n</i> function <i>f</i>, an instance of
 * <tt>RaiseArity</tt> <i>r</i> makes <i>f</i> behave like an
 * <i>m</i>':<i>n</i> function, with <i>m</i>' &gt; <i>m</i>.
 * The extra arguments given to <i>r</i> are simply ignored.
 *  
 * @author Sylvain Hallé
 * @since 0.3
 */
public class RaiseArity extends Function
{
  /**
   * The function whose arity is to be raised
   */
  /*@ non_null @*/ protected Function m_function;

  /**
   * The target input arity of the function
   */
  protected int m_inArity;

  /**
   * Creates a new instance of the function
   * @param arity The target arity
   * @param f The function to evaluate
   */
  //@ requires arity >= 0
  public RaiseArity(int arity, /*@ non_null @*/ Function f)
  {
    super();
    m_inArity = arity;
    m_function = f;
  }

  @Override
  public void evaluate(Object[] inputs, Object[] outputs)
  {
    m_function.evaluate(inputs, outputs);
  }

  @Override
  public void evaluate(Object[] inputs, Object[] outputs, Context context)
  {
    m_function.evaluate(inputs, outputs, context);
  }

  @Override
  public int getInputArity()
  {
    return m_inArity;
  }

  @Override
  public int getOutputArity()
  {
    return m_function.getOutputArity();
  }

  @Override
  public void getInputTypesFor(Set<Class<?>> classes, int index)
  {
    if (index >= m_function.getOutputArity())
    {
      classes.add(Variant.class);
    }
    else
    {
      m_function.getInputTypesFor(classes, index);
    }
  }

  @Override
  public Class<?> getOutputTypeFor(int index)
  {
    return m_function.getOutputTypeFor(index);
  }

  @Override
  public RaiseArity duplicate(boolean with_state)
  {
    return new RaiseArity(m_inArity, m_function.duplicate(with_state));
  }

  /**
   * @since 0.11
   */
  @Override
  public Object printState()
  {
    List<Object> list = new ArrayList<Object>(2);
    list.add(m_function);
    list.add(m_inArity);
    return list;
  }

  /**
   * @since 0.11
   */
  @SuppressWarnings("unchecked")
  public RaiseArity readState(Object o)
  {
    List<Object> list = (List<Object>) o;
    Function func = (Function) list.get(0);
    RaiseArity ra = new RaiseArity(((Number) list.get(1)).intValue(), func);
    return ra;
  }
}
