/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

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
package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

/**
 * Sink that accumulates events into queues. It is represented graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/tmf/QueueSink.png" alt="QueueSink">
 * 
 * @author Sylvain Hallé
 * @since 0.1
 */
@SuppressWarnings("squid:S2160")
public class QueueSink extends Sink
{
  protected Queue<Object>[] m_queues;

  public QueueSink(int in_arity)
  {
    super(in_arity);
    reset();
  }

  public QueueSink()
  {
    this(1);
  }

  @SuppressWarnings("unchecked")
  @Override
  public void reset()
  {
    super.reset();
    int arity = getInputArity();
    m_queues = new Queue[arity];
    for (int i = 0; i < arity; i++)
    {
      m_queues[i] = new ArrayDeque<Object>();
    }

  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    for (int i = 0; i < m_queues.length; i++)
    {
      Queue<Object> q = m_queues[i];
      if (inputs[i] != null)
      {
        q.add(inputs[i]);
      }
    }
    return true;
  }

  /**
   * Gets the queue corresponding to the <i>i</i>-th output of the sink
   * 
   * @param i
   *          The position of the output. Must be non-negative and less than the
   *          queue's arity.
   * @return The queue
   */
  /* @requires i >= 0 && i < m_queues.length */
  public Queue<Object> getQueue(int i)
  {
    return m_queues[i];
  }

  /**
   * Gets the queue corresponding to the first output of the sink
   * 
   * @return The queue
   */
  /* @requires m_queues.length > 0 */
  public Queue<Object> getQueue()
  {
    return getQueue(0);
  }

  /**
   * Removes the first event of all queues
   * 
   * @return A vector containing the first event of all queues, or containing null for empty queues
   */
  public Object[] remove()
  {
    Object[] out = new Object[m_queues.length];
    for (int i = 0; i < m_queues.length; i++)
    {
      Queue<Object> q = m_queues[i];
      if (q.isEmpty())
      {
        out[i] = null;
      }
      else
      {
        Object o = q.remove();
        out[i] = o;
      }
    }
    return out;
  }

  @Override
  public QueueSink duplicate(boolean with_state)
  {
    QueueSink qs = new QueueSink(getInputArity());
    if (with_state)
    {
      for (int i = 0; i < m_queues.length; i++)
      {
        qs.m_queues[i].addAll(m_queues[i]);
      }
    }
    return qs;
  }
  
  /**
   * @since 0.10.2
   */
  @Override
  public Object printState()
  {
    List<Queue<Object>> list = new ArrayList<Queue<Object>>(m_queues.length);
    for (Queue<Object> q : m_queues)
    {
      list.add(q);
    }
    return list;
  }
  
  /**
   * @since 0.10.2
   */
  @SuppressWarnings("unchecked")
  @Override
  public QueueSink readState(Object o)
  {
    List<Queue<Object>> list = (List<Queue<Object>>) o;
    QueueSink sink = new QueueSink(list.size());
    for (int i = 0; i < list.size(); i++)
    {
      sink.m_queues[i] = list.get(i);
    }
    return sink;
  }
}
