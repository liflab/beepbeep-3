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
package ca.uqac.lif.cep;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

/**
 * A {@link Future} object indicating that the computation is completed.
 * @author Sylvain Hallé
 * @since 0.9
 * @param <T> The type of the value returned by the computation
 */
public class FutureDone<T> implements Future<T>
{
  private final transient T m_value;

  public FutureDone(T value)
  {
    super();
    m_value = value;
  }

  @Override
  public boolean cancel(boolean arg0)
  {
    return true;
  }

  @Override
  public T get() throws InterruptedException, ExecutionException
  {
    return m_value;
  }

  @Override
  public T get(long arg0, TimeUnit arg1)
      throws InterruptedException, ExecutionException, TimeoutException
  {
    return m_value;
  }

  @Override
  public boolean isCancelled()
  {
    return false;
  }

  @Override
  public boolean isDone()
  {
    return true;
  }
}
