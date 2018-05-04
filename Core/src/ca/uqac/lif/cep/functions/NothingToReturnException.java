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
package ca.uqac.lif.cep.functions;

/**
 * Exception thrown when a function cannot produce a return value. This is a
 * "generic" type of exception; for example, if the function cannot return a
 * value because one of its arguments is of the wrong type, it should rather
 * throw a {@link InvalidArgumentException}.
 * 
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2166")
public class NothingToReturnException extends FunctionException
{
  /**
   * Dummy UID
   */
  private static final long serialVersionUID = 1L;

  public NothingToReturnException(Function f)
  {
    super("Function " + f.toString() + " has nothing to return for its arguments");
  }
}
