/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2022 Sylvain Hallé

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

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Stateful;
import ca.uqac.lif.cep.Pushable;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;

/**
 * Simulates the application of a "sliding window" to a trace. It is represented
 * graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/tmf/Window.png" alt="Window">
 * <p>
 * The processor takes as arguments another processor &phi; and a window width
 * <i>n</i>. It returns the result of &phi; after processing events 0 to
 * <i>n</i>-1&hellip; Then the result of (a new instance of &phi;) that processes
 * events 1 to <i>n</i>-1&hellip; and so on.
 * 
 * @author Sylvain Hallé
 * @since 0.2.1
 *
 */
@SuppressWarnings("squid:S2160")
public class Window extends AbstractWindow implements Stateful
{
  /**
   * The internal processor's input pushables
   */
  protected transient Pushable[] m_innerInputs;

  /**
   * The sink that will receive the events produced by the inner processor
   */
  protected SinkLast m_sink;

  /**
   * Creates a new window processor
   * @param in_processor The processor to run on each window
   * @param width The width of the window
   */
  public Window(Processor in_processor, int width)
  {
    super(in_processor, width);
    m_sink = new SinkLast(in_processor.getOutputArity());
    reset();
  }

  @SuppressWarnings("unchecked")
  @Override
  public void reset()
  {
    super.reset();
    int arity = getInputArity();
    m_window = new LinkedList[arity];
    m_innerInputs = new Pushable[arity];
    m_processor.reset();
    for (int i = 0; i < arity; i++)
    {
      m_window[i] = new LinkedList<Object>();
      m_innerInputs[i] = m_processor.getPushableInput(i);
    }
    m_sink.reset();
    Connector.connect(m_processor, m_sink);
  }

  @Override
  @SuppressWarnings("squid:S3516")
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    // Add the inputs to each window
    m_inputCount++;
    boolean windows_ok = true;
    int arity = inputs.length;
    for (int i = 0; i < arity; i++)
    {
      LinkedList<Object> q = m_window[i];
      q.add(inputs[i]);
      int size_diff = q.size() - m_width;
      leftTrim(size_diff, q);
      if (size_diff < 0)
      {
        // Window is still to small to compute
        windows_ok = false;
      }
    }
    Object[] out = null;
    if (windows_ok) // All windows have the proper width
    {
      m_processor.reset();
      m_sink.reset();
      int input_arity = getInputArity();
      @SuppressWarnings("unchecked")
      Future<Pushable>[] futures = new Future[m_width * input_arity];
      for (int i = 0; i < m_width; i++)
      {
        for (int j = 0; j < input_arity; j++)
        {
          // Feed
          LinkedList<Object> q = m_window[j];
          Object o = q.get(i);
          Pushable p = m_innerInputs[j];
          futures[i * input_arity + j] = p.pushFast(o);
          p.notifyEndOfTrace();
        }
        for (Future<?> f : futures)
        {
          if (f != null)
          {
            try
            {
              f.get();
            }
            catch (InterruptedException e)
            {
              throw new ProcessorException(e);
            }
            catch (ExecutionException e)
            {
              throw new ProcessorException(e);
            }
          }
        }
        out = m_sink.getLast();
      }
    }
    if (out == null)
    {
      // Don't return false, otherwise it would signal that no
      // event will every be produced in the future
      return true;
    }
    else
    {
      m_outputCount++;
      if (m_eventTracker != null)
      {
        for (int i = 1 - m_width; i <= 0; i++)
        {
          associateToInput(0, m_inputCount + i, 0, m_outputCount);
        }
      }
    }
    outputs.add(out);
    return true;
  }

  /**
   * Trims <i>n</i> events from the beginning of {@code q}
   * 
   * @param n
   *          The number of events to trim. If <i>n</i>&nbsp;&lt;1, trims nothing.
   *          If <i>n</i> is larger than the list's size, empties the list
   * @param q
   *          The queue to trim
   */
  protected static void leftTrim(int n, List<Object> q)
  {
    if (n <= 0)
    {
      return;
    }
    if (n >= q.size())
    {
      q.clear();
      return;
    }
    for (int i = 0; i < n; i++)
    {
      q.remove(0);
    }
  }

  @Override
  public Window duplicate(boolean with_state)
  {
    Window w = new Window(m_processor.duplicate(), m_width);
    if (with_state)
    {
      throw new UnsupportedOperationException(
          "Duplication with state not supported yet on this processor");
    }
    return w;
  }

  /**
   * Gets the width of the window.
   * 
   * @return The width
   */
  public int getWidth()
  {
    return m_width;
  }

  /**
   * Sets the width of the window.
   * 
   * @param m_width
   *          The width
   */
  public void setWidth(int m_width)
  {
    this.m_width = m_width;
  }

  /**
   * @since 0.11
   */
	@Override
	public Object getState()
	{
		// TODO Auto-generated method stub
		return null;
	}
}
