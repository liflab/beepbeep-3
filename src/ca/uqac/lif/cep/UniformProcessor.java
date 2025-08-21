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
package ca.uqac.lif.cep;

import ca.uqac.lif.cep.tmf.Passthrough;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Queue;

/**
 * Processor that produces exactly one output front for each input front
 * received. Descending from this class, rather than the more generic
 * {@link SynchronousProcessor}, can bring performance improvements when the
 * processor has an input/output arity of exactly 1. In such a case, the
 * {@link UnaryPullable} and {@link UnaryPushable} objects work about twice
 * as fast as {@link SynchronousProcessor.OutputPullable} and
 * {@link SynchronousProcessor.InputPushable} objects.
 * 
 * @author Sylvain Hallé
 * @since 0.6
 */
@SuppressWarnings("squid:S2160")
public abstract class UniformProcessor extends SynchronousProcessor
{
  /**
   * An array that will be used by the processor to compute its output
   */
  protected transient Object[] m_outputArray;

  /**
   * Creates a new uniform processor
   * 
   * @param in_arity
   *          The input arity
   * @param out_arity
   *          The output arity
   * @param c
   *          The processor's context (can be null)
   * @since 0.10.2
   */
  public UniformProcessor(int in_arity, int out_arity, /*@ null @*/ Context c)
  {
    super(in_arity, out_arity);
    m_outputArray = new Object[out_arity];
  }

  /**
   * Initializes a processor
   * 
   * @param in_arity
   *          The input arity
   * @param out_arity
   *          The output arity
   */
  public UniformProcessor(int in_arity, int out_arity)
  {
    this(in_arity, out_arity, null);
  }

  @Override
  protected final boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    boolean b = compute(inputs, m_outputArray);
    outputs.add(m_outputArray);
    return b;
  }

  /**
   * Computes one output events from its input events
   * 
   * @param inputs
   *          An array of input events; its length corresponds to the processor's
   *          input arity
   * @param outputs
   *          An array where the outputs are produced
   * @return A queue of vectors of output events, or null if no event could be
   *         produced
   */
  protected abstract boolean compute(Object[] inputs, Object[] outputs);

  @Override
  protected final boolean onEndOfTrace(Queue<Object[]> outputs)
  {
    Object[] outs = new Object[getOutputArity()];
    boolean b = onEndOfTrace(outs);
    if (b)
    {
      outputs.add(outs);
    }
    return b;
  }

  /**
   * Allows to describe a specific behavior when the trace of input fronts has
   * reached its end. Called in "push mode" only. In "pull mode", implementing
   * such a behavior can be done by using {@link Pullable#hasNext()} or
   * {@link Pullable#hasNextSoft()}.
   *
   * @param outputs
   *          An array where the outputs are produced
   * @return true if the processor should output one or several output fronts,
   *         false otherwise and by default.
   * @throws ProcessorException Thrown when an error occurs during the operation
   */
  protected boolean onEndOfTrace(Object[] outputs)
  {
    return false;
  }

  @Override
  public Pullable getPullableOutput(int index)
  {
    if (m_outputPullables[index] == null)
    {
      if (m_inputArity == 1 && m_outputArity == 1)
      {
        m_outputPullables[index] = new UnaryPullable();
      }
      else
      {
        m_outputPullables[index] = new OutputPullable(index);
      }
    }
    return m_outputPullables[index];
  }

  @Override
  public Pushable getPushableInput(int index)
  {
    if (m_inputPushables[index] == null)
    {
      if (m_inputArity == 1 && m_outputArity == 1)
      {
        m_inputPushables[index] = new UnaryPushable();
      }
      else
      {
        m_inputPushables[index] = new InputPushable(index);
      }
    }
    return m_inputPushables[index];
  }

  /**
   * A special type of Pushable for uniform processors with an input and output
   * arity of exactly 1. In such a case, the pushable object can operate in a much
   * simpler way than the generic {@link SynchronousProcessor.InputPushable} defined by
   * {@link SynchronousProcessor}, by foregoing the use of input and output queues
   * completely.
   * <p>
   * Simple experiments with a {@link Passthrough} processor have shown a speed
   * boost of about 3&times; compared to {@link SynchronousProcessor.InputPushable}.
   */
  public class UnaryPushable implements Pushable
  {
    @Override
    public Pushable push(Object o)
    {
    	boolean b = true;
      try
      {
        b = compute(new Object[] { o }, m_outputArray);
      }
      catch (ProcessorException e)
      {
        throw new PushableException(e);
      }
      if (m_outputPushables[0] == null)
      {
        throw new PushableException(
            "Output 0 of processor " + getProcessor() + " is connected to nothing");
      }
      m_outputPushables[0].push(m_outputArray[0]);
      if (!b)
      {
      	m_outputPushables[0].notifyEndOfTrace();	
      }
      return this;
    }

    @Override
    public void notifyEndOfTrace() throws PushableException
    {
      m_hasBeenNotifiedOfEndOfTrace[getPosition()] = true;
      if (!allNotifiedEndOfTrace())
      {
        return;
      }
      boolean b;
      try
      {
        b = onEndOfTrace(m_outputArray);
      }
      catch (ProcessorException e)
      {
        throw new PushableException(e);
      }
      if (b)
      {
        m_outputPushables[0].push(m_outputArray[0]);
      }
      for (int i = 0; i < m_outputArity; i++)
      {
        m_outputPushables[i].notifyEndOfTrace();
      }
    }

    @Override
    public UniformProcessor getProcessor()
    {
      return UniformProcessor.this;
    }

    @Override
    public int getPosition()
    {
      return 0;
    }
  }

  /**
   * A special type of Pushable for uniform processors with an input and output
   * arity of exactly 1. In such a case, the pullable object can operate in a much
   * simpler way than the generic {@link SynchronousProcessor.OutputPullable} defined by
   * {@link SynchronousProcessor}, by foregoing the use of input and output queues
   * (almost) completely.
   * <p>
   * Simple experiments with a {@link Passthrough} processor have shown a speed
   * boost of about 2.5&times; compared to {@link SynchronousProcessor.OutputPullable}.
   */
  public class UnaryPullable implements Pullable
  {

    @Override
    public Iterator<Object> iterator()
    {
      return this;
    }

    @Override
    public void remove()
    {
      throw new UnsupportedOperationException();
    }

    @Override
    public Object pullSoft()
    {
      if (!m_inputQueues[0].isEmpty())
      {
        return m_inputQueues[0].remove();
      }
      Object o = m_inputPullables[0].pullSoft();
      try
      {
        if (o == null || !compute(new Object[] { o }, m_outputArray))
        {
          return null;
        }
      }
      catch (ProcessorException e)
      {
        throw new PullableException(e);
      }
      return m_outputArray[0];
    }

    @Override
    public Object pull()
    {
      if (!m_inputQueues[0].isEmpty())
      {
        return m_inputQueues[0].remove();
      }
      if (m_inputPullables[0] == null)
      {
        throw new PullableException("Input 0 of this processor is connected to nothing",
            getProcessor());
      }
      Object o = m_inputPullables[0].pull();
      try
      {
        if (o == null || !compute(new Object[] { o }, m_outputArray))
        {
          throw new NoSuchElementException();
        }
      }
      catch (ProcessorException e)
      {
        throw new PullableException(e);
      }
      return m_outputArray[0];
    }

    @Override
    @SuppressWarnings("squid:S2272") // since() pull throws the exception
    public Object next()
    {
      return pull();
    }

    @Override
    public NextStatus hasNextSoft()
    {
      if (!m_inputQueues[0].isEmpty())
      {
        // Since we are a uniform processor, we know that the
        // existence of an input will generate an output
        return NextStatus.YES;
      }
      else
      {
        if (m_inputPullables[0] == null)
        {
          throw new PullableException("Input 0 of this processor is connected to nothing",
              getProcessor());
        }
        return m_inputPullables[0].hasNextSoft();
      }
    }

    @Override
    public boolean hasNext()
    {
      if (!m_inputQueues[0].isEmpty())
      {
        // Since we are a uniform processor, we know that the
        // existence of an input will generate an output
        return true;
      }
      else
      {
        if (m_inputPullables[0] == null)
        {
          throw new PullableException("Input 0 of this processor is connected to nothing",
              getProcessor());
        }
        return m_inputPullables[0].hasNext();
      }
    }

    @Override
    public Processor getProcessor()
    {
      return UniformProcessor.this;
    }

    @Override
    public int getPosition()
    {
      return 0;
    }

    @Override
    public void start()
    {
      UniformProcessor.this.start();
    }

    @Override
    public void stop()
    {
      UniformProcessor.this.stop();
    }

    @Override
    public void dispose()
    {
      // Nothing to do
    }

  }

}
