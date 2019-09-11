/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2019 Sylvain Hallé

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
package ca.uqac.lif.cep.util;

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Checks if an object is an instance of a given class.
 * @author Sylvain Hallé
 * @since 0.11
 */
public class InstanceOf extends UnaryFunction<Object,Boolean>
{
  /**
   * The class to compare the object against
   */
  protected Class<?> m_class;
  
  /**
   * Creates a new instance of the function
   * @param c The class to compare the object against
   */
  public InstanceOf(Class<?> c)
  {
    super(Object.class, Boolean.class);
    m_class = c;
  }
  
  @Override
  public Boolean getValue(Object o)
  {
    if (o == null)
    {
      return false;
    }
    return o.getClass().isAssignableFrom(m_class);
  }
  
  @Override
  public InstanceOf duplicate(boolean with_state)
  {
    return this;
  }
}
