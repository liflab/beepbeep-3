/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2023 Sylvain Hallé

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

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Stateful;
import ca.uqac.lif.cep.SynchronousProcessor;

import java.util.Queue;

/**
 * Inserts an event a certain number of times before letting the input events
 * through. This processor can be used to shift events of an input trace
 * forward, padding the beginning of the trace with some dummy element.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 */
@SuppressWarnings("squid:S2160")
public class Insert extends SynchronousProcessor implements Stateful
{
  /**
   * The event to be added at the beginning of the input trace
   */
  private final Object[] m_pad;

  /**
   * The number of times the pad should be inserted before the beginning of the
   * input trace
   */
  private final int m_times;

  /**
   * Whether or not the padding has already been sent
   */
  private boolean m_sentPad;

  /**
   * Instantiates a new Insert processor
   * @param times
   *          The number of times these events should be repeated before the
   *          beginning of the input trace
   * @param o
   *          The event(s) to use as padding
   */
  public Insert(int times, Object ... o)
  {
    super(o.length, o.length);
    m_pad = o;
    m_times = times;
    m_sentPad = false;
  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    if (!m_sentPad)
    {
      // Send the padding before the first input event
      for (int i = 0; i < m_times; i++)
      {
        outputs.add(m_pad);
      }
      m_sentPad = true;
    }
    outputs.add(inputs);
    return true;
  }

  @Override
  public void reset()
  {
    super.reset();
    m_sentPad = false;
  }

  @Override
  public Insert duplicate(boolean with_state)
  {
    return new Insert(m_times, m_pad);
  }

  /**
   * @since 0.11
   */
  @Override
  public Object getState()
  {
    return m_sentPad;
  }

  public Pullable getPullableOutput(int index)
  {
    if (m_outputPullables[index] == null)
    {
      m_outputPullables[index] = new InsertPullable(index);
    }
    return m_outputPullables[index];
  }

  /**
   * A {@link Pullable} object specific to the behavior of {@link Insert}.
   * It overrides the default behavior of {@link SynchronousProcessor}'s
   * pullable object, which first pulls an input event from each input pipe
   * before calling {@code compute}. In the case of {@link Insert}, input
   * pipes are not pulled if the pad has not been emitted yet.
   */
  protected class InsertPullable extends OutputPullable
  {
    /**
     * Creates a new instance of the pullable object.
     * @param index The index of the output pipe this pullable is associated
     * with
     */
    public InsertPullable(int index)
    {
      super(index);
    }

    @Override
    public boolean hasNext()
    {
      if (m_sentPad)
      {
        return super.hasNext();
      }
      for (int i = 0; i < m_times; i++)
      {
        for (int j = 0; j < m_pad.length; j++)
        {
          m_outputQueues[j].add(m_pad[j]);
        }
        m_sentPad = true;
      }
      return true;
    }
  }
  
  @Override
  public Pullable getPullableOutput(int index)
  {
  	if (m_outputPullables[index] == null)
  	{
  		m_outputPullables[index] = new InsertPullable(index);
  	}
  	return m_outputPullables[index];
  }
  
  /**
   * A {@link Pullable} object that does not pull events from upstream before
   * the events to insert have been emitted. This makes it possible to connect
   * the output of a processor to a path that leads back to one of its inputs,
   * provided that an {@link Insert} processor lies somewhere on that path.
   * 
   * @since 0.11.2
   */
  protected class InsertPullable extends OutputPullable
  {
		public InsertPullable(int index)
		{
			super(index);
		}
		
		@Override
		public boolean hasNext()
		{
			if (!m_sentPad)
			{
				for (int i = 0; i < m_times; i++)
				{
					for (int j = 0; j < m_pad.length; j++)
					{
						m_outputQueues[j].add(m_pad[j]);
					}
				}
				m_sentPad = true;
				return true;
			}
			return super.hasNext();
		}
  }
}
