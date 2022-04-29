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

import ca.uqac.lif.cep.PubliclyStateful;
import ca.uqac.lif.cep.UniformProcessor;

/**
 * Returns its input as its output. Although it seems useless,
 * <tt>Passthrough</tt> is used internally by interpreters as a
 * placeholder when building processor chains from an expression.
 * <p>
 * Graphically, this processor is represented as:
 * <p>
 * <img src="{@docRoot}/doc-files/tmf/Passthrough.png" alt="Passthrough">
 * 
 * @author Sylvain Hallé
 * @since 0.1
 */
@SuppressWarnings("squid:S2160")
public class Passthrough extends UniformProcessor implements PubliclyStateful
{
  public Passthrough(int arity)
  {
    super(arity, arity);
  }

  public Passthrough()
  {
    this(1);
  }

  @Override
  protected boolean compute(Object[] inputs, Object[] outputs)
  {
    for (int i = 0; i < inputs.length; i++)
    {
      outputs[i] = inputs[i];
      if (m_eventTracker != null)
      {
        m_eventTracker.associateToInput(getId(), i, m_inputCount, i, m_outputCount);
      }
    }
    m_inputCount++;
    m_outputCount++;
    return true;
  }

  @Override
  public Passthrough duplicate(boolean with_state)
  {
    return new Passthrough(getInputArity());
  }
  
  /**
   * @since 0.10.2
   */
  public Object printState()
  {
    return getInputArity();
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Passthrough readState(Object o)
  {
    return new Passthrough(((Number) o).intValue());
  }

	@Override
	public Object getState()
	{
		return 0;
	}
}
