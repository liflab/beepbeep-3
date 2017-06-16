/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;

public class Pump extends Processor implements Runnable
{
	/**
	 * Semaphore used to stop the pump
	 */
	private volatile boolean m_run;
	
	/**
	 * Creates a new pump
	 */
	public Pump()
	{
		super(1, 1);
	}

	@Override
	public void run()
	{
		m_run = true;
		Pullable pullable = getPullableInput(0);
		Pushable pushable = getPushableOutput(0);
		while (m_run && pullable.hasNext())
		{
			Object o = pullable.pull();
			pushable.push(o);
		}
	}
	
	@Override
	public void start()
	{
		run();
	}
	
	@Override
	public synchronized void stop()
	{
		m_run = false;
	}

	@Override
	public Pushable getPushableInput(int index) 
	{
		// You are not supposed to push to a pump
		throw new UnsupportedOperationException();
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		// You are not supposed to pull from a pump
		throw new UnsupportedOperationException();
	}

	@Override
	public Pump clone()
	{
		return new Pump();
	}
	
	
}
