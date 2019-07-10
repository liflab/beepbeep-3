/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A {@link Function} object representing the composition of multiple functions 
 * together to form a "compound" function.
 * <p>
 * A function tree has a <em>root</em>, 
 * which consists of an <i>m</i>:<i>m</i> function. This function is connected to <i>n</i> 
 * children, which can be functions or function trees themselves. The 
 * drawing below depicts a function tree that composes multiplication 
 * and addition to form a more complex function of two arguments.
 * <p>
 * <img src="{@docRoot}/doc-files/functions/FunctionTree.png" alt="FunctionTree">
 * 
 * @author Sylvain Hallé
 * @since 0.3
 */
public class FunctionTree extends Function
{
  /**
   * The function to evaluate
   */
  protected Function m_function;

  /**
   * The children function to evaluate first
   */
  protected Function[] m_children;

  /**
   * Creates a new function tree
   * 
   * @param f
   *          The function to act as the root of the tree
   */
  public FunctionTree(Function f)
  {
    super();
    m_function = f;
    m_children = new Function[f.getInputArity()];
  }

  /**
   * Creates a new function tree, by specifying the root and its immediate
   * children
   * 
   * @param functions
   *          An array of functions. The first element of the array is the
   *          function to act as the root of the tree. The size of the array must
   *          be <i>n</i>+1, where <i>n</i> is the input arity of that function.
   *          The remaining elements of the array are the functions that will be
   *          the children of the root in the resulting tree.
   */
  public FunctionTree(Function ... functions)
  {
    this(functions[0]);
    for (int i = 1; i < functions.length; i++)
    {
      setChild(i - 1, functions[i]);
    }
  }

  /**
   * Sets the <i>i</i>-th child of the tree
   * 
   * @param index
   *          The index. The method does not check ranges, so an
   *          ArrayIndexOutOfBounds exception will be thrown if attempting to set
   *          a child in an invalid position.
   * @param f
   *          The function
   * @return This tree
   */
  public FunctionTree setChild(int index, Function f)
  {
    m_children[index] = f;
    return this;
  }

  @Override
  public void evaluate(Object[] inputs, Object[] outputs, Context context)
  {
    Object[] values = new Object[m_children.length];
    for (int i = 0; i < values.length; i++)
    {
      Object[] val = new Object[1];
      m_children[i].evaluate(inputs, val, context);
      values[i] = val[0];
    }
    m_function.evaluate(values, outputs, context);
  }
  
  @Override
  public void evaluate(Object[] inputs, Object[] outputs)
  {
    evaluate(inputs, outputs, null);
  }

  @Override
  public boolean evaluatePartial(Object[] inputs, Object[] outputs, Context context)
  {
    Object[] values = new Object[m_children.length];
    for (int i = 0; i < values.length; i++)
    {
      Object[] val = new Object[1];
      if (m_children[i].evaluatePartial(inputs, val, context))
      {
        values[i] = val[0];
      }
      else
      {
        values[i] = null;
      }
    }
    return m_function.evaluatePartial(values, outputs, context);
  }

  @Override
  public boolean evaluateLazy(Object[] inputs, Object[] outputs)
  {
    return evaluatePartial(inputs, outputs, null);
  }

  @Override
  public int getInputArity()
  {
    int max_arity = 0;
    for (Function child : m_children)
    {
      if (child instanceof StreamVariable)
      {
        max_arity = Math.max(max_arity, ((StreamVariable) child).getIndex() + 1);
      }
      else
      {
        max_arity = Math.max(max_arity, child.getInputArity());
      }
    }
    return max_arity;
  }

  @Override
  public int getOutputArity()
  {
    return m_function.getOutputArity();
  }

  @Override
  public void reset()
  {
    m_function.reset();
    for (Function f : m_children)
    {
      f.reset();
    }

  }

  @Override
  public synchronized FunctionTree duplicate(boolean with_state)
  {
    FunctionTree out = new FunctionTree(m_function.duplicate(with_state));
    for (int i = 0; i < m_children.length; i++)
    {
      out.m_children[i] = m_children[i].duplicate(with_state);
    }
    return out;
  }

  @Override
  public void getInputTypesFor(Set<Class<?>> classes, int index)
  {
    for (Function f : m_children)
    {
      if (f instanceof StreamVariable)
      {
        StreamVariable ap = (StreamVariable) f;
        if (ap.getIndex() == index)
        {
          m_function.getInputTypesFor(classes, index);
        }
      }
    }
  }

  @Override
  public Class<?> getOutputTypeFor(int index)
  {
    return m_function.getOutputTypeFor(index);
  }

  @Override
  public String toString()
  {
    StringBuilder out = new StringBuilder();
    if (m_children.length == 2)
    {
      out.append("[").append(m_children[0]).append("]").append(m_function).append("[")
      .append(m_children[1]).append("]");
    }
    else
    {
      out.append(m_function).append("[");
      for (int i = 0; i < m_children.length; i++)
      {
        if (i > 0)
        {
          out.append(",");
        }
        out.append(m_children[i]);
      }
      out.append("]");
    }
    return out.toString();
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Object printState()
  {
    Map<String,Object> map = new HashMap<String,Object>();
    map.put("function", m_function);
    List<Function> children = new ArrayList<Function>(m_children.length);
    for (int i = 0; i < m_children.length; i++)
    {
      children.add(m_children[i]);
    }
    map.put("children", children);
    return map;
  }
  
  @SuppressWarnings("unchecked")
  @Override
  public FunctionTree readState(Object o)
  {
    Map<String,Object> map = (Map<String,Object>) o;
    Function f = (Function) map.get("function");
    List<Function> children = (List<Function>) map.get("children");
    FunctionTree ft = new FunctionTree(f);
    ft.m_children = new Function[children.size()];
    for (int i = 0; i < children.size(); i++)
    {
      ft.m_children[i] = children.get(i);
    }
    return ft;
  }
}
