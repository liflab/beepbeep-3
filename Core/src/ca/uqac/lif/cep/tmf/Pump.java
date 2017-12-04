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

/**
 * Processor that repeatedly pulls its input, and pushes the resulting
 * events to its output. The Pump is a way to bridge an upstream part of a
 * processor chain that works in <em>pull</em> mode, to a downstream part
 * that operates in <em>push</em> mode.
 * <p>
 * Graphically, this processor is represented as:
 * <p>
 * <a href="{@docRoot}/doc-files/tmf/Pump.png"><img
 *   src="{@docRoot}/doc-files/tmf/Pump.png"
 *   alt="Processor graph"></a>
 * <p>
 * The repeated pulling of events from its input is started by calling this
 * processor's {@link #start()} method. In the background, this will
 * instantiate a new thread, which will endlessly call <tt>pull()</tt> on
 * whatever input is connected to the pump, and then call <tt>push()</tt>
 * on whatever input is connected to it.
 * <p>
 * The opposite of the Pump is the {@link ca.uqac.lif.cep.tmf.Tank Tank}.
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class Pump extends Processor implements Runnable
{
	/**
	 * Semaphore used to stop the pump
	 */
	private volatile boolean m_run;

	/**
	 * The time interval, in milliseconds, between each pull of the
	 * pump
	 */
	protected long m_interval;

	/**
	 * Creates a new pump
	 */
	public Pump()
	{
		this(0);
	}

	/**
	 * Creates a new pump
	 * @param interval The time interval, in milliseconds, between each
	 * pull of the pump
	 */
	public Pump(long interval)
	{
		super(1, 1);
		m_interval = interval;
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
			if (m_interval >= 0)
			{
				try 
				{
					Thread.sleep(m_interval);
				}
				catch (InterruptedException e) 
				{
					// Restore interrupted state
					Thread.currentThread().interrupt();
				}
			}
		}
		pushable.notifyEndOfTrace();
	}

	@Override
	public void start()
	{
		if (!m_run)
		{
			Thread t = new Thread(this);
			t.start();
		}
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
		return new Pushable.PushNotSupported(this, index);
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		// You are not supposed to pull from a pump
		return new Pullable.PullNotSupported(this, index);
	}

	@Override
	public Pump duplicate()
	{
		return new Pump();
	}
}
