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

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SynchronousProcessor;
import java.util.Queue;

/**
 * Processor that receives two input streams; it pushes the events of a first
 * stream into a processor, and resets this processor whenever the event on the
 * second input stream is <tt>true</tt>.
 * @author Sylvain Hallé
 * 
 * @since 0.10
 */
public class ResetLast extends SynchronousProcessor
{
  /**
   * The processor to invoke on each input front
   */
  protected Processor m_processor;
  
  /**
   * The Pushable used to feed events to the underlying processor
   */
  protected Pushable m_pushable;
  
  /**
   * The sink that will store the events produced by the underlying processor
   */
  protected SinkLast m_sink;
  
  /*@ requires p.getInputArity() == 1 && p.getOutputArity() == 1 @*/
  /**
   * Creates a new reset processor.
   * @param p The processor to invoke on each input front. Must be 1:1.
   */
  public ResetLast(/*@ not_null @*/ Processor p)
  {
    super(2, 1);
    m_processor = p;
    m_sink = new SinkLast();
    Connector.connect(m_processor, m_sink);
    m_pushable = m_processor.getPushableInput();
  }
  
  @Override
  protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
  {
    boolean b = (Boolean) inputs[1];
    m_pushable.push(inputs[0]);
    if (b)
    {
      Object[] last = m_sink.getLast();
      if (last != null)
      {
        outputs.add(new Object[] {last[0]});
      }
      m_sink.reset();
      m_processor.reset();
    }
    return true;
  }

  @Override
  public ResetLast duplicate(boolean with_state)
  {
    ResetLast res = new ResetLast(m_processor.duplicate(with_state));
    if (with_state)
    {
      res.m_sink = m_sink.duplicate(with_state);
      Connector.connect(res.m_processor, res.m_sink);
    }
    return res;
  }
  
  @Override
  public void reset()
  {
    super.reset();
    m_processor.reset();
    m_sink.reset();
  }

}