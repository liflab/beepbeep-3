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
package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.SynchronousProcessor;
import ca.uqac.lif.cep.functions.Function;
import java.util.Queue;

/**
 * Discards events from an input trace based on a selection criterion. The
 * processor outputs the event if a given condition on this event evaluates
 * to true.
 * <p>
 * Graphically, this processor is represented as:
 * <p>
 * <img src="{@docRoot}/doc-files/tmf/Filter.png" alt="Filter">
 * 
 * @author Sylvain Hallé
 * @since 0.11
 * @see Filter
 */
@SuppressWarnings("squid:S2160")
public class FilterOn extends SynchronousProcessor
{
  /**
   * The condition to evaluate on each input event
   */
  protected Function m_condition;
  
  /**
   * Creates a new filter
   * @param condition The condition to evaluate on each input event
   */
  /*@ requires condition.getInputArity() == 1 @*/
  /*@ requires condition.getOutputArity() == 1 @*/
  public FilterOn(/*@ non_null @*/ Function condition)
  {
    super(1, 1);
    m_condition = condition;
  }

  @Override
  @SuppressWarnings("squid:S3516")
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    Object o = inputs[0];
    Object[] f_cond_out = new Object[1];
    m_condition.evaluate(inputs, f_cond_out);
    Object[] out = new Object[1];
    boolean b = (Boolean) f_cond_out[0];
    if (b)
    {
      out[0] = o;
    }
    else
    {
      return true;
    }
    outputs.add(out);
    return true;
  }

  @Override
  public FilterOn duplicate(boolean with_state)
  {
    return new FilterOn(m_condition.duplicate(with_state));
  }
}
