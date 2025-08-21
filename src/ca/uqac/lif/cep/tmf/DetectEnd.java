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

import java.util.Queue;

import ca.uqac.lif.cep.SynchronousProcessor;
import ca.uqac.lif.cep.functions.Function;

/**
 * Lets all input events through, and sends an "end of trace" signal when a
 * specific event is received.
 * 
 * @since 0.11
 * @author Sylvain Hallé
 */
public class DetectEnd extends SynchronousProcessor
{
	/**
	 * A flag that indicates if the end has been detected. The processor will not
	 * output any new event after that.
	 */
	protected boolean m_done;
	
	/**
	 * The function used to determine if an event is the last.
	 */
	protected Function m_condition;
	
	/**
	 * Creates a new instance of the processor.
	 * @param condition The function used to determine if an event is the last
	 */
	public DetectEnd(Function condition)
	{
		super(1, 1);
		m_condition = condition;
		m_done = false;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		if (m_done)
		{
			return false;
		}
		Object o = inputs[0];
		Object[] outs = new Object[1];
		m_condition.evaluate(inputs, outs);
		m_done = (Boolean) outs[0];
		if (m_done)
		{
			return false;
		}
		outputs.add(new Object[] {o});
		return true;
	}
	
	@Override
	public void reset()
	{
		m_done = false;
	}

	@Override
	public DetectEnd duplicate(boolean with_state)
	{
		DetectEnd e = new DetectEnd(m_condition.duplicate(with_state));
		if (with_state)
		{
			e.m_done = m_done;
		}
		return e;
	}
	
	@Override
	public String toString()
	{
		return "DetectEnd@" + hashCode();
	}
}
