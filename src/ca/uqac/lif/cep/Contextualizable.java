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
package ca.uqac.lif.cep;

/**
 * Interface implemented by all BeepBeep objects that manipulate a
 * {@link Context}.
 * @author Sylvain Hallé
 * @since 0.3
 */
public interface Contextualizable
{
  /**
   * Adds a complete context to this object
   * 
   * @param context
   *          The context to add
   */
  public void setContext(/*@ null @*/ Context context);

  /**
   * Adds an object to the object's context
   * 
   * @param key
   *          The key associated to that object
   * @param value
   *          The object
   */
  public void setContext(/*@ non_null @*/ String key, /*@ null @*/ Object value);

  /**
   * Gets the context associated to this object
   * 
   * @return The context
   */
  public /*@ non_null @*/ Context getContext();
}
