package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.SynchronousProcessor;
import java.util.Queue;

/**
 * Outputs only the last event received.
 * 
 * @author Sylvain Hallé
 * @since 0.8 
 */
public class KeepLast extends SynchronousProcessor
{
  protected Object[] m_lasts;

  public KeepLast(int in_arity)
  {
    super(in_arity, in_arity);
    m_lasts = null;
  }

  public KeepLast()
  {
    this(1);
  }

  @Override
  public KeepLast duplicate(boolean with_state)
  {
    return new KeepLast(m_inputArity);
  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    if (m_lasts == null)
    {
      m_lasts = new Object[m_inputArity];
    }
    // Keep the last front of events
    for (int i = 0; i < inputs.length; i++)
    {
      m_lasts[i] = inputs[i];
    }
    // But don't return anything
    return true;
  }

  @Override
  protected boolean onEndOfTrace(Queue<Object[]> outputs)
  {
    if (m_lasts != null)
    {
      outputs.add(m_lasts);
      return true;
    }
    return false;
  }
}
