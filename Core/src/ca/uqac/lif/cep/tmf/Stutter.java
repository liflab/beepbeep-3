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

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SynchronousProcessor;
import java.util.Queue;

/**
 * Repeats each input event a specified number of times.
 * 
 * @author Sylvain Hallé
 */
public class Stutter extends SynchronousProcessor
{
  /**
   * The number of times each input event is repeated
   */
  protected int m_numReps = 1;
  
  /**
   * Creates a new Stutter processor
   * @param num_reps The number of times each input event will be repeated
   * in the output
   */
  public Stutter(int num_reps)
  {
    super(1, 1);
    m_numReps = num_reps;
  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    for (int i = 0; i < m_numReps; i++)
    {
      outputs.add(inputs);
    }
    return true;
  }

  @Override
  public Processor duplicate(boolean with_state)
  {
    return new Stutter(m_numReps);
  }
}