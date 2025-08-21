/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import java.util.Queue;

/**
 * A special type of {@link Sink} that discards everything it receives.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class BlackHole extends Sink
{
  public BlackHole()
  {
    this(1);
  }
  
  public BlackHole(int arity)
  {
    super(arity);
  }
  
  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    return false;
  }

  @Override
  public BlackHole duplicate(boolean with_state)
  {
    return new BlackHole();
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
  public BlackHole readState(Object o)
  {
    return new BlackHole(((Number) o).intValue());
  }
}