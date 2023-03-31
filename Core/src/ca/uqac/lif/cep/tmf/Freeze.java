/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2022 Sylvain Hallé

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
import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.util.Lists.MathList;

import java.util.ArrayList;
import java.util.List;

/**
 * Repeatedly outputs the first event it has received. {@code Freeze} works
 * a bit like {@link ca.uqac.lif.cep.functions.Constant Constant}; however, while
 * {@code Constant} is
 * given the event to output, {@code Freeze} waits for a first event,
 * outputs it, and then outputs that event whenever some new input comes in.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class Freeze extends UniformProcessor implements Stateful
{
  /**
   * The event front to freeze
   */
  protected transient Object[] m_output;

  /**
   * Creates a new freeze processor
   */
  public Freeze()
  {
    super(1, 1);
  }

  @Override
  public void reset()
  {
    super.reset();
    m_output = null;
  }

  @Override
  protected boolean compute(Object[] inputs, Object[] outputs)
  {
    if (m_output == null)
    {
      m_output = inputs;
    }
    outputs[0] = m_output[0];
    return true;
  }

  @Override
  public Freeze duplicate(boolean with_state)
  {
    return new Freeze();
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Object printState()
  {
    if (m_output != null)
    {
      List<Object> front = new ArrayList<Object>(m_output.length);
      for (Object o : m_output)
      {
        front.add(o);
      }
      return front;
    }
    return null;
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Freeze readState(Object o)
  {
    Freeze f = new Freeze();
    if (o != null)
    {
      @SuppressWarnings("unchecked")
      List<Object> front = (List<Object>) o;
      f.m_output = new Object[front.size()];
      for (int i = 0; i < f.m_output.length; i++)
      {
        f.m_output[i] = front.get(i);
      }
    }
    return f;
  }
  
  /**
   * @since 0.11
   */
  @Override
  public Object getState()
  {
  	if (m_output == null)
  	{
  		return null;
  	}
  	MathList<Object> list = new MathList<Object>();
  	for (Object o : m_output)
  	{
  		list.add(o);
  	}
  	return list;
  }
}
