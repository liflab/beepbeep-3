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
 * A Future object whose termination and output value depends on the
 * termination and output values of multiple other Future objects.
 * @author Sylvain Hallé
 * @since 0.9
 *
 * @param <T> The output type of this future
 * @param <U> The output type of the multiple "sub-futures" this Future
 * depends on
 */
public abstract class CompoundFuture<T,U> implements Future<T> 
{
  /**
   * The array of "sub-futures" this Future depends on
   */
  protected Future<U>[] m_futures;

  public CompoundFuture(/*@ non_null @*/ Future<U>[] futures)
  {
    super();
    m_futures = futures;
  }

  @Override
  public boolean cancel(boolean may_interrupt_if_running)
  {
    boolean b = false;
    for (Future<?> f : m_futures)
    {
      b = b | f.cancel(may_interrupt_if_running);
    }
    return b;
  }

  @Override
  public boolean isCancelled()
  {
    for (Future<?> f : m_futures)
    {
      if (f.isCancelled())
      {
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean isDone()
  {
    for (Future<?> f : m_futures)
    {
      if (!f.isDone())
      {
        return false;
      }
    }
    return true;
  }

  @Override
  public T get() throws InterruptedException, ExecutionException
  {
    @SuppressWarnings("unchecked")
    U[] values = (U[]) new Object[m_futures.length];
    return compute(values);
  }

  @Override
  public T get(long timeout, TimeUnit unit) 
      throws InterruptedException, ExecutionException, TimeoutException 
  {
    @SuppressWarnings("unchecked")
    U[] values = (U[]) new Object[m_futures.length];
    long max_ns = TimeUnit.NANOSECONDS.convert(timeout, unit);
    long start_time = System.nanoTime();
    long elapsed = 0;
    int i = 0;
    while (elapsed < max_ns && i < m_futures.length)
    {
      long time_budget = max_ns - elapsed;
      values[i] = m_futures[i].get(time_budget, TimeUnit.NANOSECONDS);
      elapsed = System.nanoTime() - start_time;
      i++;
    }
    if (i < m_futures.length)
    {
      // We have not succeeded in completing all sub-futures in time
      throw new TimeoutException();
    }
    return compute(values);
  }

  /**
   * Computes the return value of this Future, based on the return values
   * of each sub-future.
   * @param values The values returned by each sub-future
   * @return The output value to compute
   */
  public abstract T compute(U[] values);

}
