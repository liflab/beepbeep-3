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

import java.util.Queue;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * Returns one input event and discards the next <i>n</i>-1. The value <i>n</i>
 * is called the <em>decimation interval</em>.
 * However, a mode can be specified in order to output the <i>n</i>-<i>i</i>th input
 * event if it is the last event of the trace and it has not been output already.
 *
 * @author Sylvain Hallé
 */
public class CountDecimate extends SingleProcessor
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = -1528026169905098741L;

	/**
	 * The decimation interval
	 */
	private final int m_interval;

	/**
	 * Indicates if the last inputs should be output even if its index does not correspond to the interval
	 */
	protected final boolean m_shouldOutputLastInputsAnyway;

	/**
	 * The last input received
	 */
	protected Object[] m_lastInputs;

	/**
	 * Index of last event received
	 */
	protected int m_current;

	public CountDecimate()
	{
		this(1);
	}

	public CountDecimate(int interval, boolean shouldOutputLastInputsAnyway) {
		super(1, 1);
		m_interval = interval;
		m_shouldOutputLastInputsAnyway = shouldOutputLastInputsAnyway;
		m_lastInputs = null;
		m_current = 0;
	}

	public CountDecimate(int interval)
	{
		this(interval, false);
	}

	@Override
	public void reset()
	{
		super.reset();
		m_current = 0;
	}

	@Override
	@SuppressWarnings("squid:S3516")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		Object[] out = null;
		m_inputCount++;
		if (m_current == 0)
		{
			out = inputs;
			m_lastInputs = null;
		}
		else if(m_shouldOutputLastInputsAnyway)
		{
			m_lastInputs = inputs;
		}
		m_current = (m_current + 1) % m_interval;
		if (out == null)
		{
			return true;
		}
		m_outputCount++;
		if (m_eventTracker != null)
		{
			if (m_inputCount < 0)
			{
				m_inputCount += m_interval;
			}
			for (int i = 0; i < inputs.length; i++)
			{
				associateToInput(i, m_inputCount - 1, i, m_outputCount - 1);
			}
		}
		outputs.add(out);
		return true;
	}

	@Override
	protected boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException
	{
		if(!m_shouldOutputLastInputsAnyway || m_lastInputs == null)
			return super.onEndOfTrace(outputs);

		outputs.add(m_lastInputs);
		m_lastInputs = null;

		return true;
	}

	@Override
	public CountDecimate duplicate()
	{
		return new CountDecimate(m_interval);
	}

	public int getInterval() {
		return m_interval;
	}
}
