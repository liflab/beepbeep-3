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

import java.util.HashMap;
import java.util.Map;

import ca.uqac.lif.cep.Stateful;

/**
 * Returns one input event and discards the next <i>n</i>-1. The value <i>n</i> is called
 * the <strong>decimation interval</strong>. However, a mode can be specified in order to
 * output the <i>n</i>-th input event if it is the last event of the trace and it has
 * not been output already.
 * <p>
 * It is represented graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/tmf/CountDecimate.png" alt="CountDecimate">
 *
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class CountDecimate extends Decimate implements Stateful
{
  /**
   * The decimation interval
   */
  private final int m_interval;

  /**
   * Index of last event received
   */
  protected int m_current;

  /**
   * Creates a new count decimate processor with a decimation interval of 1
   */
  public CountDecimate()
  {
    this(1);
  }

  /**
   * Creates a new count decimate processor
   * 
   * @param interval
   *          The decimation interval
   */
  public CountDecimate(int interval)
  {
    this(interval, false);
  }

  /**
   * Creates a new count decimate processor
   *
   * @param interval
   *          The decimation interval
   * @param should_process_last_inputs
   *          Default to false. Indicates if the processor should output the last
   *          input events of the trace even if it does not correspond to the
   *          decimation interval.
   */
  public CountDecimate(int interval, boolean should_process_last_inputs)
  {
    super(should_process_last_inputs);
    m_interval = interval;
    m_current = 0;
  }

  /**
   * Gets the decimation interval
   * 
   * @return The interval
   */
  public int getInterval()
  {
    return m_interval;
  }

  @Override
  protected boolean shouldOutput()
  {
    return m_current == 0;
  }

  @Override
  protected void postCompute()
  {
    m_current = (m_current + 1) % m_interval;
  }

  @Override
  public void reset()
  {
    super.reset();
    m_current = 0;
  }

  @Override
  public CountDecimate duplicate(boolean with_state)
  {
    return new CountDecimate(m_interval, m_shouldProcessLastInputs);
  }

  /**
   * @since 0.10.2
   */
  @Override
  protected Object printState()
  {
    Map<String,Object> map = new HashMap<String,Object>();
    map.put("interval", m_interval);
    map.put("current", m_current);
    map.put("process-last", m_shouldProcessLastInputs);
    return map;
  }
  
  /**
   * @since 0.10.2
   */
  @SuppressWarnings("unchecked")
  @Override
  protected CountDecimate readState(Object o)
  {
    Map<String,Object> map = (Map<String,Object>) o;
    CountDecimate cd = new CountDecimate(((Number) map.get("interval")).intValue(), 
        (Boolean) map.get("process-last"));
    cd.m_current = ((Number) map.get("current")).intValue();
    return cd;
  }
  
  /**
   * @since 0.11
   */
  @Override
  public Object getState()
  {
  	return m_current;
  }
}
