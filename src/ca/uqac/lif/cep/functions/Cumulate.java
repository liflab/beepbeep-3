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
package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.Stateful;

/**
 * Creates a cumulative processor out of a cumulative function. This is simply a
 * {@link ApplyFunction} whose function is of a specific type (a
 * {@link CumulativeFunction}).
 * <p>
 * It is represented graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/functions/Cumulate.png" alt="Cumulate">
 * <p>
 * In earlier versions of the library, this class was called
 * {@code CumulativeProcessor}.
 * @author Sylvain Hallé
 * @since 0.1
 */
public class Cumulate extends ApplyFunction implements Stateful
{
  // This constructor is used for deserialization.
  private Cumulate()
  {
    super(null);
  }
  
  /**
   * Creates a new instance of the processor from a cumulative function.
   * @param f The cumulative function
   * @since 0.1
   */
  public Cumulate(CumulativeFunction<?> f)
  {
    super(f);
  }
  
  /**
   * Creates a new instance of the processor from a binary function.
   * @param f The binary function
   * @since 0.11
   */
  @SuppressWarnings({ "unchecked", "rawtypes" })
	public Cumulate(BinaryFunction<?,?,?> f)
  {
    super(new CumulativeFunction(f));
  }

  public void cloneInto(Cumulate c, boolean with_state)
  {
    super.cloneInto(c, with_state);
  }
  
  @Override
  public Cumulate duplicate(boolean with_state)
  {
    Cumulate c = new Cumulate((CumulativeFunction<?>) m_function.duplicate(with_state));
    cloneInto(c, with_state);
    return c;
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Object printState()
  {
    return m_function;
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Cumulate readState(Object o)
  {
    CumulativeFunction<?> f = (CumulativeFunction<?>) o;
    return new Cumulate(f);
  }
  
  /**
   * @since 0.11
   */
  @Override
  public Object getState()
  {
  	return ((CumulativeFunction<?>) m_function).getLastValue();
  }
}
