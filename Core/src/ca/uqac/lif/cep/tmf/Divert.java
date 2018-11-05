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
package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.Future;

/**
 * Diverts an input stream to one of many downstream processor
 * chains.
 * <p>
 * More specifically, the divert processor is a 1:1 processor,
 * to which multiple downstream processors can be linked using calls
 * to {@link Connector#connect}. However, only a single of them is actually
 * "active"; that is, if one pushes an event to the Divert processor, this
 * event will be pushed to a single one of the downstream processors.
 * Which one is determined by a number called the "flow index"; this index
 * can be changed at runtime using {@link #divertTo(int) divertTo()}.
 * As a rule, each processor connected downstream to the Divert processor
 * is given an increasing integer flow index, starting at 0 for the first
 * downstream processor.
 * <p>
 * On the contrary, any of the connected downstream processors can pull
 * events. An event pulled by a downstream processor will be received by
 * this processor only; the other downstream processors are not notified
 * of this pull.
 * <p> 
 * The processor is represented graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/tmf/Divert.png" alt="Divert">
 * 
 * @author Sylvain Hallé
 */
public class Divert extends Processor
{
  /**
   * The list of downstream {@link Pushable}s connected to this processor 
   */
  protected List<Pushable> m_downstreamPushables;
  
  /**
   * The {@link Pushable} connected to the upstream processor
   */
  protected Pushable m_inputPushable;
  
  /**
   * The instance of the special {@link Pullable} given to all
   * downstream processors
   */
  protected Pullable m_outputPullable;
  
  /**
   * The index of the flow the input stream will be diverted to
   */
  protected int m_flowIndex = 0;
  
  /**
   * Creates a new divert processor.
   */
  public Divert()
  {
    super(1, 1);
    m_downstreamPushables = new ArrayList<Pushable>();
    m_inputPushable = null;
    m_outputPullable = null;
  }
  
  /**
   * Diverts the downstream flow
   * @param index The index of the flow to divert the output to
   * @return This processor
   */
  /*@ non_null @*/ public Divert divertTo(int index)
  {
    m_flowIndex = index;
    return this;
  }

  @Override
  public Divert duplicate(boolean with_state)
  {
    return new Divert();
  }
  
  @Override
  public synchronized void setPushableOutput(int i, /*@ non_null @*/ Pushable p)
  {
    m_downstreamPushables.add(p);
  }

  @Override
  public Pushable getPushableInput(int index)
  {
    if (index > 0)
    {
      throw new IndexOutOfBoundsException(
          "This processor does not have a pushable at index " + index);
    }
    if (m_inputPushable == null)
    {
      m_inputPushable = new DivertPushable();
    }
    return m_inputPushable;
  }

  @Override
  public Pullable getPullableOutput(int index)
  {
    if (index > 0)
    {
      throw new IndexOutOfBoundsException(
          "This processor does not have a pushable at index " + index);
    }
    if (m_outputPullable == null)
    {
      m_outputPullable = new DivertPullable();
    }
    return m_outputPullable;
  }
  
  /**
   * Implementation of the {@link Pushable} interface for the {@link Divert}
   * processor.
   */
  public class DivertPushable implements Pushable
  {

    @Override
    public Pushable push(Object o)
    {
      m_downstreamPushables.get(m_flowIndex).push(o);
      return this;
    }

    @Override
    public Future<Pushable> pushFast(Object o)
    {
      return m_downstreamPushables.get(m_flowIndex).pushFast(o);
    }

    @Override
    public void notifyEndOfTrace() throws PushableException
    {
      m_downstreamPushables.get(m_flowIndex).notifyEndOfTrace();
    }

    @Override
    public Divert getProcessor()
    {
      return Divert.this;
    }

    @Override
    public int getPosition()
    {
      return 0;
    }
  }
  
  /**
   * Implementation of the {@link Pullable} interface for the {@link Divert}
   * processor.
   */
  public class DivertPullable implements Pullable
  {

    @Override
    public Iterator<Object> iterator()
    {
      return this;
    }

    @Override
    public Object pullSoft()
    {
      return m_inputPullables[0].pullSoft();
    }

    @Override
    public Object pull()
    {
      return m_inputPullables[0].pull();
    }

    @Override
    public Object next()
    {
      return m_inputPullables[0].next();
    }

    @Override
    public NextStatus hasNextSoft()
    {
      return m_inputPullables[0].hasNextSoft();
    }

    @Override
    public boolean hasNext()
    {
      return m_inputPullables[0].hasNext();
    }

    @Override
    public Divert getProcessor()
    {
      return Divert.this;
    }

    @Override
    public int getPosition()
    {
      return 0;
    }

    @Override
    public void start()
    {
      // Nothing to do
    }

    @Override
    public void stop()
    {
      // Nothing to do
    }

    @Override
    public void dispose()
    {
      // Nothing to do
    }
  }
}
