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
 * Outputs only the last event received.
 * 
 * @author Sylvain Hallé
 * @since 0.8 
 */
public class KeepLast extends SynchronousProcessor
{
  protected Object[] m_lasts;

  public KeepLast(int in_arity)
  {
    super(in_arity, in_arity);
    m_lasts = null;
  }

  public KeepLast()
  {
    this(1);
  }

  @Override
  public KeepLast duplicate(boolean with_state)
  {
    return new KeepLast(m_inputArity);
  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    if (m_lasts == null)
    {
      m_lasts = new Object[m_inputArity];
    }
    // Keep the last front of events
    for (int i = 0; i < inputs.length; i++)
    {
      m_lasts[i] = inputs[i];
    }
    // But don't return anything
    return true;
  }

  @Override
  protected boolean onEndOfTrace(Queue<Object[]> outputs)
  {
    if (m_lasts != null)
    {
      outputs.add(m_lasts);
      return true;
    }
    return false;
  }
}
