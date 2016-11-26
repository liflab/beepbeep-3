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
package ca.uqac.lif.cep.concurrency;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;

public class NonBlockingPusher extends Processor
{
	protected Processor m_processor;
	
	public NonBlockingPusher(Processor p)
	{
		super(1, 1);
		m_processor = p;
	}

	@Override
	public Pushable getPushableInput(int index) 
	{
		if (index == 0)
		{
			Pusher p = new OnDemandPusher(m_processor.getPushableInput(0));
			ThreadPushable tp = new ThreadPushable(p);
			return tp;
		}
		return null;
	}

	@Override
	public Pullable getPullableOutput(int index) 
	{
		return m_processor.getPullableOutput(index);
	}

	@Override
	public NonBlockingPusher clone() 
	{
		NonBlockingPusher nbp = new NonBlockingPusher(m_processor.clone());
		nbp.setContext(m_context);
		return nbp;
	}
	
	@Override
	public void setContext(Context c)
	{
		if (c == null)
		{
			return;
		}
		if (m_context == null)
		{
			m_context = new Context();
		}
		m_context.putAll(c);
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		if (m_context == null)
		{
			m_context = new Context();
		}
		m_context.put(key, value);
	}
}
