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

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;

/**
 * Joins multiple traces as a single one. The splicer is given
 * multiple input traces. It feeds the events of the first one
 * until it does not yield any new event. Then it starts feeding
 * events of the second one, and so on.
 * <p>
 * Currently, the splicer is implemented as a 0:n processor, and
 * the processors it is given must have an input arity of 0.
 * 
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class Splice extends Source
{
	/**
	 * The list of processors to splice together
	 */
	protected Processor[] m_processors;

	/**
	 * The index of the processor we are currently reading from
	 */
	protected int m_processorIndex;

	/**
	 * The pullables of the processor we are currently reading from
	 */
	protected transient Pullable[] m_pullables;

	/**
	 * 
	 * @param processors
	 */
	public Splice(Processor ... processors)
	{
		super(processors[0].getOutputArity());
		m_processors = processors;
		m_processorIndex = 0;
		m_pullables = new Pullable[processors[0].getOutputArity()];
		setPullablesTo(0);
	}

	protected void setPullablesTo(int index)
	{
		Processor p = m_processors[index];
		for (int i = 0; i < m_pullables.length; i++)
		{
			m_pullables[i] = p.getPullableOutput(i);
		}
	}

	@Override
	public void reset()
	{
		m_processorIndex = 0;
		for (Processor p : m_processors)
		{
			p.reset();
		}
		setPullablesTo(0);
	}

	@Override
	public void setContext(Context context)
	{
		super.setContext(context);
		for (Processor p : m_processors)
		{
			p.setContext(context);
		}
	}

	@Override
	public void setContext(String key, Object value)
	{
		super.setContext(key, value);
		for (Processor p : m_processors)
		{
			p.setContext(key, value);
		}
	}

	@Override
	@SuppressWarnings("squid:S1168")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		if (m_processorIndex >= m_processors.length)
		{
			return false;
		}
		Object[] out = new Object[m_pullables.length];
		for (int index = m_processorIndex; index < m_processors.length; index++)
		{
			boolean has_null = false;
			for (int i = 0; i < m_pullables.length; i++)
			{
				boolean status = m_pullables[i].hasNext();
				if (!status)
				{
					// No use in trying further
					has_null = true;
					break;
				}
				Object o = m_pullables[i].pull();
				if (o == null)
				{
					has_null = true;
					break;
				}
				out[i] = o;
			}
			if (!has_null)
			{
				outputs.add(out);
				return true;
			}
			m_processorIndex++;
			if (m_processorIndex < m_processors.length)
			{
				setPullablesTo(m_processorIndex);
			}
		}
		return false;
	}

	@Override
	public Splice duplicate()
	{
		return new Splice(m_processors);
	}
}
