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
package ca.uqac.lif.cep.epl;

import java.util.Queue;

import ca.uqac.lif.cep.Passthrough;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;

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
	protected Queue<Object[]> compute(Object[] inputs)
	{
		// Don't do anything, as the computation is taken care of by
		// the SentinelPullable
		return null;
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		return new SentinelPullable();
	}
	
	protected class SentinelPullable implements Pullable
	{
		//protected Pullable m_pullable;
		
		public SentinelPullable()
		{
			super();
		}

		@Override
		public Object pull() 
		{
			if (m_done)
			{
				return null;
			}
			Object o = m_inputPullables[0].pull();
			if (o != null)
			{
				m_lastReceived = o;
				return null;
			}
			m_done = true;
			return m_lastReceived;
		}

		@Override
		public Object pullHard() 
		{
			if (m_done)
			{
				return null;
			}
			for (int tries = 0; tries < Pullable.s_maxRetries; tries++)
			{
				Object o = m_inputPullables[0].pullHard();
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
		public NextStatus hasNext() 
		{
			if (m_done)
			{
				return NextStatus.NO;
			}
			return m_inputPullables[0].hasNext();
		}
		
		@Override
		public NextStatus hasNextHard() 
		{
			if (m_done)
			{
				return NextStatus.NO;
			}
			return m_inputPullables[0].hasNextHard();
		}

		@Override
		public int getPullCount() 
		{
			return m_inputPullables[0].getPullCount();
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
	}
	
}
