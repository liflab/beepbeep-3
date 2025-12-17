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

import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.Context;
import java.util.Set;

/**
 * A function of two arguments, the first of which is a 1:1 function; it
 * applies this function to the second argument and returns the result.
 * @author Sylvain Hallé
 * @since 0.10.2
 */
public class ApplyFunctionArgument extends Function
{
  /**
   * A single visible instance of the function
   */
  public static final transient ApplyFunctionArgument instance = new ApplyFunctionArgument();
  
  /**
   * Creates a new instance of the function. This constructor
   * should not be called directly.
   */
  protected ApplyFunctionArgument()
  {
    super();
  }

  @Override
  public ApplyFunctionArgument duplicate(boolean with_state)
  {
    return this;
  }

  @Override
  public void evaluate(Object[] inputs, Object[] outputs, Context context)
  {
    if (!(inputs[0] instanceof Function))
    {
      throw new FunctionException("First input of this processor is not a Function");
    }
    Function f = (Function) inputs[0];
    Object arg = inputs[1];
    Object[] in_args = new Object[] {arg};
    Object[] out_args = new Object[1];
    f.evaluate(in_args, out_args, context);
    outputs[0] = out_args[0];
  }

  @Override
  public int getInputArity()
  {
    return 2;
  }

  @Override
  public int getOutputArity()
  {
    return 1;
  }

  @Override
  public void getInputTypesFor(Set<Class<?>> classes, int index)
  {
    if (index == 0)
    {
      classes.add(Function.class);
    }
    if (index == 1)
    {
      classes.add(Variant.class);
    }
  }

  @Override
  public Class<?> getOutputTypeFor(int index)
  {
    return Variant.class;
  }
}