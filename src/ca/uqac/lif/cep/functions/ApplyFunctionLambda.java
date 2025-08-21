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

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.UniformProcessor;

public class ApplyFunctionLambda extends UniformProcessor
{
  protected LambdaEvaluable m_evaluable;
  
  protected Class<?> m_returnType;
  
  public ApplyFunctionLambda(UnaryLambdaEvaluable e, Class<?> return_type)
  {
    super(1, 1);
    m_evaluable = new LambdaEvaluable(e);
    m_returnType = return_type;
  }
  
  public ApplyFunctionLambda(UnaryLambdaEvaluable e)
  {
    this(e, Object.class);
  }
  
  public ApplyFunctionLambda(BinaryLambdaEvaluable e, Class<?> return_type)
  {
    super(2, 1);
    m_evaluable = new LambdaEvaluable(e);
    m_returnType = return_type;
  }
  
  public ApplyFunctionLambda(BinaryLambdaEvaluable e)
  {
    this(e, Object.class);
  }
  
  @Override
  protected boolean compute(Object[] inputs, Object[] outputs)
  {
    outputs[0] = m_evaluable.evaluate(inputs);
    return true;
  }

  @Override
  public Processor duplicate(boolean with_state)
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
  
  protected static class LambdaEvaluable
  {
    UnaryLambdaEvaluable m_unary = null;
    
    BinaryLambdaEvaluable m_binary = null;
    
    public LambdaEvaluable(UnaryLambdaEvaluable e)
    {
      super();
      m_unary = e;
    }
    
    public LambdaEvaluable(BinaryLambdaEvaluable e)
    {
      super();
      m_binary = e;
    }
    
    public Object[] evaluate(Object ... inputs)
    {
      if (m_unary != null)
      {
        return new Object[] {m_unary.evaluate(inputs[0])};
      }
      if (m_binary != null)
      {
        return new Object[] {m_binary.evaluate(inputs[0], inputs[1])};
      }
      throw new Error("not unary or binary");
    }
  }
}
