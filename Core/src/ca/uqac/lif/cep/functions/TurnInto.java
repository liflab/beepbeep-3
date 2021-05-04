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
package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.UniformProcessor;
import java.util.Set;

/**
 * Processor that turns any event into a predefined object. It is represented
 * graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/functions/TurnInto.png" alt="TurnInto">
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class TurnInto extends UniformProcessor
{
  /**
   * The event to turn everything into
   */
  protected final Object m_event;

  /**
   * Instantiates a new function processor
   * 
   * @param o
   *          The computable object responsible for the computation
   */
  public TurnInto(Object o)
  {
    super(1, 1);
    m_event = o;
  }

  @Override
  protected boolean compute(Object[] inputs, Object[] outputs)
  {
    outputs[0] = m_event;
    return true;
  }

  @Override
  public synchronized TurnInto duplicate(boolean with_state)
  {
    TurnInto out = new TurnInto(m_event);
    duplicateInto(out);
    return out;
  }

  @Override
  public final void getInputTypesFor(/*@ non_null @*/ Set<Class<?>> classes, int index)
  {
    classes.add(Object.class);
  }

  @Override
  public final synchronized Class<?> getOutputType(int index)
  {
    return m_event.getClass();
  }

  @Override
  public String toString()
  {
    return "Turn into " + m_event;
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Object printState()
  {
    return m_event;
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public TurnInto readState(Object o)
  {
    return new TurnInto(o);
  }
}
