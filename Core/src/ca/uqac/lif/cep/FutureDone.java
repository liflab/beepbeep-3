package ca.uqac.lif.cep;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

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
