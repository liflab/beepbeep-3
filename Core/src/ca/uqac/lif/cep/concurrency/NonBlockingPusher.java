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
import ca.uqac.lif.cep.concurrency.ThreadManager.ManagedThread;

/**
 * Wrapper around a processor that makes its calls to
 * {@link Pushable#push(Object) push()} non blocking.
 * 
 * @author Sylvain Hallé
 */
public class NonBlockingPusher extends Processor
{
	/**
	 * The processor to which events will be pushed
	 */
	protected final Processor m_processor;

	/**
	 * The thread manager to get instances of threads
	 */
	protected final ThreadManager m_threadManager;

	/**
	 * The thread in which the pipeline thread is running
	 */
	protected ManagedThread m_managedThread;

	/**
	 * The pushable to which events will be pushed
	 */
	protected Pushable m_pushable;

	/**
	 * A reference to the pushable this processor should send its output to
	 */
	protected Pushable m_pushableOutput;

	/**
	 * A reference to the pullable this processor should pull its input from
	 */
	protected Pullable m_pullableInput;

	/**
	 * Creates a new non-blocking pusher
	 * @param p The processor to wrap
	 * @param manager The thread manager that will coordinate the granting of
	 *   threads for this processor
	 */
	public NonBlockingPusher(Processor p, ThreadManager manager)
	{
		super(1, 1);
		m_processor = p;
		if (manager != null)
		{
			m_threadManager = manager;
		}
		else
		{
			if (ThreadManager.defaultManager != null)
			{
				m_threadManager = ThreadManager.defaultManager;
			}
			else
			{
				m_threadManager = null;
			}
		}
	}

	public NonBlockingPusher(Processor p)
	{
		this(p, ThreadManager.defaultManager);
	}

	@Override
	synchronized public void setPushableOutput(int index, Pushable p)
	{
		m_pushableOutput = p;
		m_processor.setPushableOutput(index, p);
	}

	@Override
	public synchronized Pullable getPullableInput(int index)
	{
		return m_pullableInput;
	}

	@Override
	public synchronized void setPullableInput(int index, Pullable p)
	{
		m_processor.setPullableInput(index, p);
		m_pullableInput = p;
	}

	@Override
	public synchronized Pushable getPushableOutput(int index)
	{
		return m_pushableOutput;
	}

	@Override
	public synchronized Pushable getPushableInput(int index)
	{
		if (index == 0)
		{
			if (m_pushable != null)
			{
				return m_pushable;
			}
			Pushable original_pushable = m_processor.getPushableInput(0);
			m_pushable = new NewThreadPushable(this, original_pushable, m_threadManager);
			//ThreadPushable.tryPushable(original_pushable, m_threadManager);
			return m_pushable;
		}
		return null;
	}

	@Override
	public synchronized Pullable getPullableOutput(int index)
	{
		return m_processor.getPullableOutput(index);
	}

	@Override
	public synchronized NonBlockingPusher clone()
	{
		Processor new_processor = m_processor.clone();
		NonBlockingPusher nbp = new NonBlockingPusher(new_processor, m_threadManager);
		nbp.setContext(m_context);
		return nbp;
	}

	@Override
	public synchronized void setContext(Context c)
	{
		super.setContext(c);
		m_processor.setContext(c);
	}

	@Override
	public synchronized void setContext(String key, Object value)
	{
		super.setContext(key, value);
		m_processor.setContext(key, value);
	}
}
