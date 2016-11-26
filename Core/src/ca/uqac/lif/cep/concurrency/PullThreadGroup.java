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

import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Pullable;

public class PullThreadGroup extends GroupProcessor 
{
	protected ThreadPullable m_pullable;
	
	public PullThreadGroup(int in_arity, int out_arity) 
	{
		super(in_arity, out_arity);
		m_pullable = null;
	}
	
	@Override
	public final Pullable getPullableOutput(int index)
	{
		if (index != 0)
		{
			// For all outputs except number 0, return normal pullable
			return super.getPullableInput(index);
		}
		// For output 0, wrap pullable into a ThreadPullable
		if (m_pullable == null)
		{
			m_pullable = new ThreadPullable(new ContinuousPoller(m_outputPullables.get(index)));
		}
		return new ProxyPullable(m_pullable, index);
	}
	
	@Override
	public void start()
	{
		super.start();
		m_pullable.start();
	}
	
	@Override
	public void stop()
	{
		super.stop();
		m_pullable.stop();
	}

}
