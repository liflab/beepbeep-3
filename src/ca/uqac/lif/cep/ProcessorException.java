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
 * Generic class for any exception thrown in the lifecycle of a processor.
 * 
 * @author Sylvain Hallé
 * @since 0.6
 */
public class ProcessorException extends RuntimeException
{
  /**
   * Dummy UID
   */
  private static final long serialVersionUID = 1L;

  /**
   * Creates an exception from a throwable object
   * 
   * @param t
   *          The throwable object
   */
  public ProcessorException(Throwable t)
  {
    super(t);
  }

  /**
   * Creates an exception from a string message
   * 
   * @param message
   *          The message
   */
  public ProcessorException(String message)
  {
    super(message);
  }
}
