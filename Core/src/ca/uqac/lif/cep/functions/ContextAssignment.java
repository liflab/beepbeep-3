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

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Contextualizable;

/**
 * An object that assigns a value to a specific key in a
 * {@link ca.uqac.lif.cep.Context Context} object.
 * @author Sylvain Hallé
 */
public class ContextAssignment
{
  /**
   * The name of the context element to modify
   */
  /*@ non_null @*/ protected String m_lvalue;

  /**
   * The function computing the value to assign to the context element. It is
   * assumed that this function has an output arity of 1.
   */
  /*@ non_null @*/ protected Function m_value;

  /**
   * Creates a new context assignment
   * @param left The context key
   * @param right The value to assign to this key
   */
  public ContextAssignment(/*@ non_null @*/ String left, /*@ non_null @*/ Function right)
  {
    super();
    m_lvalue = left;
    m_value = right;
  }

  /**
   * Gets the name of the context element to modify
   * 
   * @return The variable
   */
  /*@ pure non_null @*/ public String getVariable()
  {
    return m_lvalue;
  }

  /**
   * Gets the function computing the value to assign to the context element.
   * 
   * @return The function
   */
  /*@ pure non_null @*/ public Function getAssignment()
  {
    return m_value;
  }

  /**
   * Assigns a value to a context element
   * 
   * @param inputs
   *          The inputs to evaluate the assignment function
  * @param outputs
   *          An array in which the outputs the the assignment function
   *          are placed
   * @param context
   *          The context to update @ Any exception occurring when assigning a
   *          value to the context element
   */
  /*@ pure @*/ public void assign(/*@ non_null @*/ Object[] inputs, 
      /*@ non_null @*/ Object[] outputs, /*@ non_null @*/ Context context)
  {
    m_value.evaluate(inputs, outputs, context);
    context.put(m_lvalue, outputs[0]);
  }

  /**
   * Updates the context of an object
   * 
   * @param inputs
   *          The inputs to evaluate the assignment function
  * @param outputs
   *          An array in which the outputs the the assignment function
   *          are placed
   * @param c
   *          The object
   */
  /*@ pure @*/ public void assign(/*@ non_null @*/ Object[] inputs, 
      /*@ non_null @*/ Object[] outputs, /*@ non_null @*/ Contextualizable c)
  {
    Context context = c.getContext();
    assign(inputs, outputs, context);
    c.setContext(context);
  }

  @Override
  public String toString()
  {
    return m_lvalue + ":=" + m_value;
  }
}
