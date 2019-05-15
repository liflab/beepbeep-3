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
package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SynchronousProcessor;

import java.util.Queue;

/**
 * 
 * @author Sylvain Hallé
 * @since 0.10.2
 */
public class Pad extends SynchronousProcessor
{
  protected Processor m_processor;
  
  protected Object[] m_front;
  
  protected int m_times;
  
  protected int m_numPad;
  
  protected Pushable[] m_innerPushables;
  
  protected QueueSink m_sink;
  
  /**
   * Creates a Pad processor
   * @param p The processor whose output is to be padded
   * @param times The number of times to pad
   * @param front The event front to pad before the output of <tt>p</tt>
   */
  public Pad(Processor p, int times, Object ... front)
  {
    super(p.getInputArity(), p.getOutputArity());
    m_processor = p;
    m_times = times;
    m_front = front;
    m_numPad = 0;
    m_innerPushables = new Pushable[p.getInputArity()];
    for (int i = 0; i < m_innerPushables.length; i++)
    {
      m_innerPushables[i] = m_processor.getPushableInput(i);
    }
    m_sink = new QueueSink(m_processor.getOutputArity());
    Connector.connect(m_processor, m_sink);
  }

  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    for (int i = 0; i < inputs.length; i++)
    {
      m_innerPushables[i].push(inputs[i]);
    }
    if (m_numPad < m_times)
    {
      m_numPad++;
      outputs.add(m_front);
      return true;
    }
    boolean loop = true;
    while (loop)
    {
      for (int i = 0; i < m_sink.getInputArity(); i++)
      {
        if (m_sink.getQueue(i).isEmpty())
        {
          loop = false;
          break;
        }
      }
      if (loop)
      {
        Object[] out = new Object[m_sink.getInputArity()];
        for (int i = 0; i < m_sink.getInputArity(); i++)
        {
          out[i] = m_sink.getQueue(i).remove();
        }
        outputs.add(out);
      }
    }
    return true;
  }
  
  @Override
  public void reset()
  {
    m_numPad = 0;
    m_processor.reset();
  }

  @Override
  public Pad duplicate(boolean with_state)
  {
    return new Pad(m_processor.duplicate(), m_times, m_front);
  }
}
