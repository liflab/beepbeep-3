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

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.EventTracker;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * Represents a stateless <i>m</i>-to-<i>n</i> function.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
public abstract class Function implements DuplicableFunction, Printable, Readable
{
  /**
   * The maximum input arity that a function can have
   */
  public static final int s_maxInputArity = 10;

  /**
   * Evaluates the outputs of the function, given some inputs
   * 
   * @param inputs
   *          The arguments of the function. The size of the array should be equal
   *          to the function's declared input arity.
   * @param outputs
   *          The outputs of the function. The size of the array should
   *          be equal to the function's declared output arity.
   * @param context
   *          The context in which the evaluation is done. If the function's
   *          arguments contains placeholders, they will be replaced by the
   *          corresponding object fetched from this map before evaluating the
   *          function
   */
  /*@ pure @*/ public void evaluate(/*@ non_null @*/ Object[] inputs, 
      /*@ non_null @*/ Object[] outputs, /*@ null @*/ Context context)
  {
    evaluate(inputs, outputs, context, null);
  }
  
  /**
   * Evaluates the outputs of the function, given some inputs
   * 
   * @param inputs
   *          The arguments of the function. The size of the array should be equal
   *          to the function's declared input arity.
   * @param outputs
   *          The outputs of the function. The size of the array should
   *          be equal to the function's declared output arity.
   * @param context
   *          The context in which the evaluation is done. If the function's
   *          arguments contains placeholders, they will be replaced by the
   *          corresponding object fetched from this map before evaluating the
   *          function
   * @param tracker
   *          An event tracker to record associations between inputs and outputs.
   *          This argument is optional and may be null.
   */
  /*@ pure @*/ public abstract void evaluate(/*@ non_null @*/ Object[] inputs, 
      /*@ non_null @*/ Object[] outputs, /*@ null @*/ Context context,
      /*@ null @*/ EventTracker tracker);

  /**
   * Evaluates the outputs of the function, given some inputs
   * 
   * @param inputs
   *          The arguments of the function. The size of the array should be equal
   *          to the function's declared input arity.
   * @param outputs
   *          The outputs of the function. The size of the array should
   *          be equal to the function's declared output arity. @ Any exception
   *          that may occur during the evaluation of a function
   */
  /*@ pure @*/ public void evaluate(/*@ non_null @*/ Object[] inputs, 
      /*@ non_null @*/ Object[] outputs)
  {
    evaluate(inputs, outputs, null);
  }

  /**
   * Evaluates the outputs of the function, given some inputs
   * 
   * @param inputs
   *          The arguments of the function. The size of the array should be equal
   *          to the function's declared input arity.
   * @param outputs
   *          The outputs of the function. The size of the array should
   *          be equal to the function's declared output arity.
   * @param context
   *          The context in which the evaluation is done. If the function's
   *          arguments contains placeholders, they will be replaced by the
   *          corresponding object fetched from this map before evaluating the
   *          function
   * @return {@code true} if the function succeeded in producing an output
   *          value, {@code false} otherwise
   */
  /*@ pure @*/ public boolean evaluatePartial(/*@ non_null @*/ Object[] inputs, 
      /*@ non_null @*/ Object[] outputs, /*@ null @*/ Context context)
  {
    // Defer the call to evaluate if any input is null
    for (int i = 0; i < inputs.length; i++)
    {
      if (inputs[i] == null)
      {
        return false;
      }
    }
    evaluate(inputs, outputs, context);
    return true;
  }

  /**
   * Attempts a lazy evaluation of the function, given some inputs
   * 
   * @param inputs
   *          The arguments of the function. The size of the array should be equal
   *          to the function's declared input arity.
   * @param outputs
   *          The outputs of the function. The size of the array should
   *          be equal to the function's declared output arity. @ Any exception
   *          that may occur during the evaluation of a function
   * @return {@code true} if the function succeeded in producing an output
   *          value, {@code false} otherwise 
   */
  /*@ pure @*/ public boolean evaluateLazy(/*@ non_null @*/ Object[] inputs, 
      /*@ non_null @*/ Object[] outputs)
  {
    return evaluatePartial(inputs, outputs, null);
  }

  /**
   * Gets the function's input arity, i.e. the number of arguments it takes.
   * 
   * @return The input arity
   */
  /*@ ensures \result >= 0 @*/
  /*@ pure @*/ public abstract int getInputArity();

  /**
   * Gets the function's output arity, i.e. the number of elements it outputs. (We
   * expect that most functions will have an output arity of 1.)
   * 
   * @return The output arity
   */
  /*@ ensures \result >= 0 @*/
  /*@ pure @*/ public abstract int getOutputArity();

  /**
   * Resets the function to its initial state. In the case of a stateless
   * function, nothing requires to be done.
   */
  /*@ pure @*/ public void reset()
  {
    // Do nothing
  }

  /**
   * Populates the set of classes accepted by the function for its <i>i</i>-th
   * input
   * 
   * @param classes
   *          The set of to fill with classes
   * @param index
   *          The index of the input to query
   */
  /*@ pure @*/ public abstract void getInputTypesFor(/*@ non_null @*/ Set<Class<?>> classes, 
      int index);

  /**
   * Returns the type of the events produced by the function for its <i>i</i>-th
   * output
   * 
   * @param index
   *          The index of the output to query
   * @return The type of the output
   */
  /*@ pure @*/ public abstract Class<?> getOutputTypeFor(int index);

  @Override
  /*@ pure non_null @*/ public final Function duplicate()
  {
    return duplicate(false);
  }

  @Override
  /*@ pure non_null @*/ public abstract Function duplicate(boolean with_state);

  /**
   * @since 0.10.2
   */
  @Override
  public Object print(ObjectPrinter<?> printer)
  {
    Map<String,Object> map = new HashMap<String,Object>();
    map.put("contents", printState());
    try
    {
      return printer.print(map);
    }
    catch (PrintException e)
    {
      throw new FunctionException(e);
    }
  }

  /**
   * Produces an object that represents the state of the current function.
   * A concrete function should override this method to add whatever state
   * information that needs to be preserved in the serialization process.
   * @return Any object representing the function's state 
   * (including {@code null})
   * @since 0.10.2
   */
  protected Object printState()
  {
    return null;
  }

  /**
   * Reads the content of a function from a serialized object.
   * @param reader An object reader
   * @param o The object to read from
   * @return The deserialized function
   * @throws FunctionException If the read operation failed for some reason
   */
  @SuppressWarnings("unchecked")
  @Override
  public final Function read(ObjectReader<?> reader, Object o) throws FunctionException
  {
    Map<String, Object> contents = null;
    try
    {
      contents = (Map<String,Object>) reader.read(o);
    }
    catch (ReadException e)
    {
      throw new FunctionException(e);
    }
    Function f = null;
    if (contents.containsKey("contents"))
    {
      Object o_contents = contents.get("contents");
      try
      {
        f = readState(o_contents);
      }
      catch (UnsupportedOperationException e)
      {
        throw new FunctionException(e);
      }
    }
    if (f == null)
    {
      throw new FunctionException("The function returned null with being deserialized");
    }
    return f;
  }

  /**
   * Reads the state of a function and uses it to create a new instance
   * @param o The object containing the function's state
   * @return A new function instance
   * @since 0.10.2
   */
  protected Function readState(Object o)
  {
    throw new UnsupportedOperationException("This function does not support deserialization");
  }
}
