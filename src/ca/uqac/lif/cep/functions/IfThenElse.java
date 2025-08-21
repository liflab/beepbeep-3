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
 * Function that acts as an if-then-else. If its first input is true, it returns
 * its second input; otherwise it returns its third input. It is represented
 * graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/functions/IfThenElse.png" alt="IfThenElse">
 * 
 * @author Sylvain Hallé
 * @since 0.6
 */
public class IfThenElse extends Function
{
  /**
   * The unique visible instance of this function
   */
  public static final transient IfThenElse instance = new IfThenElse();

  protected IfThenElse()
  {
    super();
  }

  @Override
  public void evaluate(Object[] inputs, Object[] outputs, Context context, EventTracker tracker)
  {
    try
    {
      if ((Boolean) inputs[0])
      {
        outputs[0] = inputs[1];
        if (tracker != null)
        {
          tracker.associateToInput(-1, 0, 0, 0, 0);
          tracker.associateToInput(-1, 1, 0, 0, 0);
        }
      }
      else
      {
        outputs[0] = inputs[2];
        if (tracker != null)
        {
          tracker.associateToInput(-1, 0, 0, 0, 0);
          tracker.associateToInput(-1, 2, 0, 0, 0);
        }
      }
    }
    catch (ClassCastException e)
    {
      throw new InvalidArgumentException(this, 0);
    }
  }

  @Override
  public int getInputArity()
  {
    return 3;
  }

  @Override
  public int getOutputArity()
  {
    return 1;
  }

  @Override
  public void reset()
  {
    // Nothing to do
  }

  @Override
  public IfThenElse duplicate(boolean with_state)
  {
    return instance;
  }

  @Override
  public void getInputTypesFor(Set<Class<?>> classes, int index)
  {
    if (index == 0)
    {
      classes.add(Boolean.class);
    }
    else
    {
      classes.add(Variant.class);
    }
  }

  @Override
  public Class<?> getOutputTypeFor(int index)
  {
    return Variant.class;
  }

  @Override
  public IfThenElse readState(Object o)
  {
    return instance;
  }
}
