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

import java.util.ArrayDeque;
import java.util.Iterator;
import java.util.Queue;
import java.util.concurrent.Future;

/**
 * Processor that handles its inputs asynchronously.
 * @author Sylvain Hallé
 */
public abstract class AsynchronousProcessor extends Processor 
{
  /**
   * A queue object that will be passed to the {@link #compute(Object[], Queue)}
   * method
   */
  protected final transient Queue<Object[]> m_tempQueue;

  /**
   * An array of input pushables
   */
  protected final transient Pushable[] m_inputPushables;

  /**
   * An array of output pullables
   */
  protected transient Pullable[] m_outputPullables;

  /**
   * Indicates whether the processor has been notified of the end of trace or not
   */
  protected boolean m_hasBeenNotifiedOfEndOfTrace;

  /**
   * Counts how many input fronts have been processed
   */
  protected int m_inFrontsProcessed = 0;

  /**
   * Counts how many input events have been received on each pipe
   */
  protected int[] m_inputEventsReceived;

  /**
   * Initializes a processor
   * 
   * @param in_arity
   *          The input arity
   * @param out_arity
   *          The output arity
   */
  public AsynchronousProcessor(int in_arity, int out_arity)
  {
    super(in_arity, out_arity);
    m_tempQueue = new ArrayDeque<Object[]>(1);
    m_inputPushables = new Pushable[in_arity];
    m_outputPullables = new Pullable[out_arity];
    m_inFrontsProcessed = 0;
    m_inputEventsReceived = new int[in_arity];
    m_hasBeenNotifiedOfEndOfTrace = false;
  }

  @Override
  public void reset()
  {
    m_outputPullables = new Pullable[m_outputArity];
    m_inFrontsProcessed = 0;
    m_inputEventsReceived = new int[m_inputArity];
    m_hasBeenNotifiedOfEndOfTrace = false;
  }

  @Override
  public synchronized Pushable getPushableInput(int index)
  {
    if (m_inputPushables[index] == null)
    {
      m_inputPushables[index] = new InputPushable(index);
    }
    return m_inputPushables[index];
  }

  @Override
  public synchronized Pullable getPullableOutput(int index)
  {
    if (m_outputPullables[index] == null)
    {
      m_outputPullables[index] = new OutputPullable(index);
    }
    return m_outputPullables[index];
  }

  protected class InputPushable implements Pushable
  {
    /**
     * The index of the input pipe this pushable is connected to
     */
    protected int m_index;

    public InputPushable(int index)
    {
      super();
      m_index = index;
    }

    @Override
    public Pushable push(Object o)
    {
      // TODO Auto-generated method stub
      return null;
    }

    @Override
    public Future<Pushable> pushFast(Object o)
    {
      push(o);
      return Pushable.NULL_FUTURE;
    }

    @Override
    public void notifyEndOfTrace() throws PushableException
    {
      // TODO Auto-generated method stub
    }

    @Override
    public Processor getProcessor() 
    {
      return AsynchronousProcessor.this;
    }

    @Override
    public int getPosition()
    {
      return m_index;
    }
  }

  protected class OutputPullable implements Pullable
  {
    /**
     * The index of the input pipe this pullable is connected to
     */
    protected int m_index;

    public OutputPullable(int index)
    {
      super();
      m_index = index;
    }

    @Override
    public Iterator<Object> iterator()
    {
      // TODO Auto-generated method stub
      return null;
    }

    @Override
    public Object pullSoft() 
    {
      // TODO Auto-generated method stub
      return null;
    }

    @Override
    public Object pull() 
    {
      // TODO Auto-generated method stub
      return null;
    }

    @Override
    public Object next()
    {
      // TODO Auto-generated method stub
      return null;
    }

    @Override
    public NextStatus hasNextSoft()
    {
      // TODO Auto-generated method stub
      return null;
    }

    @Override
    public boolean hasNext() 
    {
      // TODO Auto-generated method stub
      return false;
    }

    @Override
    public Processor getProcessor() 
    {
      // TODO Auto-generated method stub
      return null;
    }

    @Override
    public int getPosition()
    {
      // TODO Auto-generated method stub
      return 0;
    }

    @Override
    public void start()
    {
      // TODO Auto-generated method stub

    }

    @Override
    public void stop()
    {
      // TODO Auto-generated method stub

    }

    @Override
    public void dispose()
    {
      // TODO Auto-generated method stub

    }
    
    @Override
    public void remove()
    {
      throw new UnsupportedOperationException("This operation is not supported on this Pullable.");
    }
  }

  /**
   * Computes one or more output events from its input events
   * 
   * @param inputs
   *          An array of input events; its length corresponds to the processor's
   *          input arity
   * @param outputs
   *          A queue of arrays of objects. The processor should push arrays into
   *          this queue for every output front it produces. The size of each
   *          array should be equal to the processor's output arity, although this
   *          is not enforced.
   * @return {@code true} if this processor may output other events in the
   * future, {@code false} otherwise
   */
  protected abstract boolean compute(Object[] inputs, Queue<Object[]> outputs);

}
