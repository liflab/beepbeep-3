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
import java.util.Queue;

/**
 * Discards the first <i>n</i> events of the input, and outputs the remaining ones.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class Trim extends SynchronousProcessor
{
  /**
   * How many events to ignore at the beginning of the trace
   */
  protected final int m_delay;
  
  /**
   * No-args constructor. Useful only for deserialization.
   */
  private Trim()
  {
    super(1, 1);
    m_delay = 0;
  }

  /**
   * Creates a new delay processor.
   * 
   * @param delay
   *          The number of events from the input trace to discard
   */
  public Trim(int delay)
  {
    super(1, 1);
    m_delay = delay;
  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    if (m_inputCount >= getDelay())
    {
      outputs.add(inputs);
      if (m_eventTracker != null)
      {
        for (int i = 0; i < inputs.length; i++)
        {
          m_eventTracker.associateToInput(getId(), i, m_inputCount, i, m_outputCount);
        }
      }
      m_outputCount++;
    }
    m_inputCount++;
    return true;
  }

  @Override
  public Trim duplicate(boolean with_state)
  {
    Trim t = new Trim(getDelay());
    if (with_state)
    {
      t.m_inputCount = m_inputCount;
      t.m_outputCount = m_outputCount;
    }
    return t;
  }

  /**
   * Gets the delay associated to the trim processor
   * @return The delay
   */
  public int getDelay()
  {
    return m_delay;
  }
  
  /**
   * @since 0.11
   */
  @Override
  protected Object printState()
  {
    return m_delay;
  }
  
  /**
   * @since 0.11
   */
  @Override
  protected Trim readState(Object o)
  {
    int delay = ((Number) o).intValue();
    return new Trim(delay);
  }
}
