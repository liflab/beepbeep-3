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
package ca.uqac.lif.cep.util;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.EventTracker;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * A container object for Boolean functions.
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class Booleans
{
  private Booleans()
  {
    // Utility class
  }

  public static final transient And and = And.instance;

  public static final transient Or or = Or.instance;

  public static final transient Implies implies = Implies.instance;

  public static final transient Not not = Not.instance;

  /**
   * Implementation of the logical conjunction
   * 
   * @author Sylvain Hallé
   */
  public static class And extends BinaryFunction<Boolean, Boolean, Boolean>
  {
    public static final transient And instance = new And();

    private And()
    {
      super(Boolean.class, Boolean.class, Boolean.class);
    }

    @Override
    public Boolean getValue(Boolean x, Boolean y)
    {
      return x.booleanValue() && y.booleanValue();
    }
    
    @Override
    protected void trackAssociations(Boolean x, Boolean y, Boolean z, EventTracker tracker)
    {
      if (!x)
      {
        tracker.associateToOutput(-1, 0, 0, 0, 0);
      }
      else if (!y)
      {
        tracker.associateToOutput(-1, 1, 0, 0, 0);
      }
      else
      {
        tracker.associateToOutput(-1, 0, 0, 0, 0);
        tracker.associateToOutput(-1, 1, 0, 0, 0);
      }
    }

    @Override
    public boolean evaluatePartial(Object[] inputs, Object[] outputs, Context context)
    {
      if (inputs[0] != null && ((Boolean) inputs[0]) == false)
      {
        outputs[0] = false;
        return true;
      }
      if (inputs[1] != null && ((Boolean) inputs[1]) == false)
      {
        outputs[0] = false;
        return true;
      }
      if (inputs[0] != null && inputs[1] != null)
      {
        outputs[0] = ((Boolean) inputs[0]) && ((Boolean) inputs[1]);
        return true;
      }
      return false;
    }

    @Override
    public String toString()
    {
      return "∧";
    }
  }

  /**
   * Implementation of the logical implication
   * 
   * @author Sylvain Hallé
   */
  public static class Implies extends BinaryFunction<Boolean, Boolean, Boolean>
  {
    public static final transient Implies instance = new Implies();

    private Implies()
    {
      super(Boolean.class, Boolean.class, Boolean.class);
    }

    @Override
    public Boolean getValue(Boolean x, Boolean y)
    {
      return !x.booleanValue() || y.booleanValue();
    }

    @Override
    public boolean evaluatePartial(Object[] inputs, Object[] outputs, Context context)
    {
      if (inputs[0] != null && ((Boolean) inputs[0]) == false)
      {
        outputs[0] = true;
        return true;
      }
      if (inputs[1] != null && ((Boolean) inputs[1]) == true)
      {
        outputs[0] = true;
        return true;
      }
      if (inputs[0] != null && inputs[1] != null)
      {
        outputs[0] = !((Boolean) inputs[0]) || ((Boolean) inputs[1]);
        return true;
      }
      return false;
    }
    
    @Override
    protected void trackAssociations(Boolean x, Boolean y, Boolean z, EventTracker tracker)
    {
      if (!x)
      {
        tracker.associateToOutput(-1, 0, 0, 0, 0);
      }
      else if (y)
      {
        tracker.associateToOutput(-1, 1, 0, 0, 0);
      }
      else
      {
        tracker.associateToOutput(-1, 0, 0, 0, 0);
        tracker.associateToOutput(-1, 1, 0, 0, 0);
      }
    }

    @Override
    public String toString()
    {
      return "→";
    }
  }

  /**
   * Implementation of the logical disjunction
   * 
   * @author Sylvain Hallé
   */
  public static class Or extends BinaryFunction<Boolean, Boolean, Boolean>
  {
    public static final transient Or instance = new Or();

    private Or()
    {
      super(Boolean.class, Boolean.class, Boolean.class);
    }

    @Override
    public Boolean getValue(Boolean x, Boolean y)
    {
      return x.booleanValue() || y.booleanValue();
    }
    
    @Override
    protected void trackAssociations(Boolean x, Boolean y, Boolean z, EventTracker tracker)
    {
      if (x)
      {
        tracker.associateToOutput(-1, 0, 0, 0, 0);
      }
      else if (y)
      {
        tracker.associateToOutput(-1, 1, 0, 0, 0);
      }
      else
      {
        tracker.associateToOutput(-1, 0, 0, 0, 0);
        tracker.associateToOutput(-1, 1, 0, 0, 0);
      }
    }

    @Override
    public boolean evaluatePartial(Object[] inputs, Object[] outputs, Context context)
    {
      if (inputs[0] != null && ((Boolean) inputs[0]) == true)
      {
        outputs[0] = true;
        return true;
      }
      if (inputs[1] != null && ((Boolean) inputs[1]) == true)
      {
        outputs[0] = true;
        return true;
      }
      if (inputs[0] != null && inputs[1] != null)
      {
        outputs[0] = ((Boolean) inputs[0]) || ((Boolean) inputs[1]);
        return true;
      }
      return false;
    }

    @Override
    public String toString()
    {
      return "∨";
    }
  }

  /**
   * Implementation of the logical negation
   * 
   * @author Sylvain Hallé
   */
  public static class Not extends UnaryFunction<Boolean, Boolean>
  {
    public static final transient Not instance = new Not();

    private Not()
    {
      super(Boolean.class, Boolean.class);
    }

    @Override
    public Boolean getValue(Boolean x)
    {
      return !x.booleanValue();
    }

    @Override
    public String toString()
    {
      return "¬";
    }
  }

  /**
   * Attempts to convert an object into a Boolean
   * 
   * @param o
   *          The object
   * @return The Boolean value
   */
  public static boolean parseBoolValue(Object o)
  {
    if (o instanceof Boolean)
    {
      return (Boolean) o;
    }
    else if (o instanceof String)
    {
      String s = (String) o;
      return s.compareToIgnoreCase("true") == 0 || s.compareToIgnoreCase("T") == 0
          || s.compareToIgnoreCase("1") == 0;
    }
    if (o instanceof Number)
    {
      Number n = (Number) o;
      return Math.abs(n.doubleValue()) >= 0.00001;
    }
    // When in doubt, return false
    return false;
  }
}
