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
package ca.uqac.lif.cep.functions;

import java.util.Set;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.EventTracker;

/**
 * A function defined based on a lambda expression
 * @author Sylvain Hallé
 */
public class FunctionLambda extends Function
{
  UnaryLambdaEvaluable m_unary = null;
  
  BinaryLambdaEvaluable m_binary = null;
  
  protected Class<?> m_returnType = Object.class;
  
  public FunctionLambda(UnaryLambdaEvaluable e)
  {
    super();
    m_unary = e;
  }
  
  public FunctionLambda(BinaryLambdaEvaluable e, Class<?> return_type)
  {
    super();
    m_binary = e;
    m_returnType = return_type;
  }
  
  public FunctionLambda(BinaryLambdaEvaluable e)
  {
    this(e, Object.class);
  }
  
  public FunctionLambda setReturnType(Class<?> c)
  {
    m_returnType = c;
    return this;
  }

  @Override
  public FunctionLambda duplicate(boolean with_state)
  {
    return this;
  }
  
  public interface UnaryLambdaEvaluable
  {
    public Object evaluate(Object o);
  }
  
  public interface BinaryLambdaEvaluable
  {
    public Object evaluate(Object o1, Object o2);
  }

  @Override
  public void evaluate(Object[] inputs, Object[] outputs, Context context, EventTracker tracker)
  {
    if (m_unary != null)
    {
      outputs[0] = m_unary.evaluate(inputs[0]);
    }
    if (m_binary != null)
    {
      outputs[0] = m_binary.evaluate(inputs[0], inputs[1]);
    }
  }

  @Override
  public int getInputArity()
  {
    if (m_binary != null)
    {
      return 2;
    }
    return 1;
  }

  @Override
  public int getOutputArity()
  {
    return 1;
  }

  @Override
  public void getInputTypesFor(Set<Class<?>> classes, int index)
  {
    classes.add(Object.class);
  }

  @Override
  public Class<?> getOutputTypeFor(int index)
  {
    return m_returnType;
  }
}
