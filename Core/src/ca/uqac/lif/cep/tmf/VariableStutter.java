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
package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.SynchronousProcessor;
import java.util.Queue;

/**
 * Processor that repeats input events a number of times based on
 * a control signal.
 * @author Sylvain Hallé
 */
public class VariableStutter extends SynchronousProcessor
{
  /**
   * Creates a new variable stutter processor
   */
  public VariableStutter()
  {
    super(2, 1);
  }
  
  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    float x = ((Number) inputs[0]).floatValue();
    int n = ((Number) inputs[1]).intValue();
    for (int i = 0; i < n; i++)
    {
      outputs.add(new Object[] {x});
    }
    return true;
  }

  @Override
  public VariableStutter duplicate(boolean with_state)
  {
    return new VariableStutter();
  }
}