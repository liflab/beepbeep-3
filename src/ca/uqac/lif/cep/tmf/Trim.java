/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2025 Sylvain Hallé

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

import ca.uqac.lif.cep.Stateful;
import ca.uqac.lif.cep.SynchronousProcessor;

import java.util.HashMap;
import java.util.Map;
import java.util.Queue;

/**
 * Discards the first <i>n</i> events of the input, and outputs the remaining ones.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class Trim extends SynchronousProcessor implements Stateful
{
  /**
   * How many events to ignore at the beginning of the trace
   */
  protected final int m_delay;
  
  /**
	 * Number of output events produced so far.
	 */
  protected int m_inputCount;
  
  /**
   * No-args constructor. Useful only for deserialization.
   */
  private Trim()
  {
    super(1, 1);
    m_delay = 0;
    m_inputCount = 0;
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
   * @since 0.10.2
   */
  @Override
  protected Object printState()
  {
    Map<String, Integer> state = new HashMap<>();
    state.put("delay", m_delay);
    state.put("inputCount", m_inputCount);
    return state;
  }
  
  /**
   * @since 0.10.2
   */
  @SuppressWarnings("unchecked")
	@Override
  protected Trim readState(Object o)
  {
  	Map<String, Number> state = (Map<String, Number>) o;
  	int delay = state.get("delay").intValue();
  	Trim t = new Trim(delay);
  	t.m_inputCount = state.get("inputCount").intValue();
  	return t;
  }

  /**
   * @since 0.11
   */
	@Override
	public Object getState()
	{
		return Math.max(0, m_delay - m_inputCount);
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_inputCount = 0;
	}
}
