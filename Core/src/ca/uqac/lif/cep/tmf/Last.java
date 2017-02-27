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

import java.util.Iterator;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;

/**
 * Processor that only returns the <em>last</em> element of its input trace.
 * The processor detects this by looking for the <tt>null</tt> event. When
 * it receives it, it outputs the last event received before <tt>null</tt>.
 * 
 * @author Sylvain Hallé
 *
 */
public class Last extends Passthrough
{
	/**
	 * The last event received
	 */
	protected Object m_lastReceived;

	/**
	 * Whether the processor has output something
	 */
	protected boolean m_done;

	public Last()
	{
		super(1);
		m_done = false;
	}

	@Override
	public void reset()
	{
		m_lastReceived = null;
		m_done = false;
	}

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs)
	{
		// Don't do anything, as the computation is taken care of by
		// the SentinelPullable
		return false;
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		return new SentinelPullable();
	}

	protected class SentinelPullable implements Pullable
	{
		public SentinelPullable()
		{
			super();
		}

		@Override
		public void remove()
		{
			// Cannot remove an event on a pullable
			throw new UnsupportedOperationException();
		}

		@Override
		public Object pullSoft()
		{
			if (m_done)
			{
				return null;
			}
			Object o = m_inputPullables[0].pullSoft();
			if (o != null)
			{
				m_lastReceived = o;
				return null;
			}
			m_done = true;
			return m_lastReceived;
		}

		@Override
		@SuppressWarnings("squid:S1168")
		public Object pull()
		{
			if (m_done)
			{
				return null;
			}
			for (int tries = 0; tries < Pullable.s_maxRetries; tries++)
			{
				Object o = m_inputPullables[0].pull();
				if (o != null)
				{
					m_lastReceived = o;
				}
				else
				{
					m_done = true;
					return m_lastReceived;
				}
			}
			return null;
		}

		@Override
		public final Object next()
		{
			return pull();
		}

		@Override
		public NextStatus hasNextSoft()
		{
			if (m_done)
			{
				return NextStatus.NO;
			}
			return m_inputPullables[0].hasNextSoft();
		}

		@Override
		public boolean hasNext()
		{
			if (m_done)
			{
				return false;
			}
			return m_inputPullables[0].hasNext();
		}

		@Override
		public Processor getProcessor()
		{
			return Last.this;
		}

		@Override
		public int getPosition()
		{
			return m_inputPullables[0].getPosition();
		}

		@Override
		public Iterator<Object> iterator()
		{
			return this;
		}

		@Override
		public void start()
		{
			for (Pullable p : m_inputPullables)
			{
				p.start();
			}
		}

		@Override
		public void stop()
		{
			for (Pullable p : m_inputPullables)
			{
				p.stop();
			}
		}

		@Override
		public void dispose()
		{
			for (Pullable p : m_inputPullables)
			{
				p.dispose();
			}
		}
	}

}
