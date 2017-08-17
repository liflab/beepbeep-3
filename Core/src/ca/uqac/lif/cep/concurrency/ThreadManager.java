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
package ca.uqac.lif.cep.concurrency;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class ThreadManager implements Runnable
{
	/**
	 * An instance of thread manager used as a default. The default
	 * thread manager forbids the use of threads.
	 */
	public static final ThreadManager defaultManager = new ThreadManager(0);

	/**
	 * The set of threads managed by this manager
	 */
	protected volatile Set<ManagedThread> m_threads;

	/**
	 * A lock to access the thread set
	 */
	protected Lock m_threadsLock;

	/**
	 * The maximum number of threads this manager is allowed to keep
	 * at any moment
	 */
	protected int m_maxThreads = 2;

	/**
	 * The time (in milliseconds) between refreshes of the internal
	 * state of the manager
	 */
	protected static final long s_sleepInterval = 30;

	/**
	 * Whether the manager is running
	 */
	protected volatile boolean m_run = false;

	/**
	 * Total number of threads requested. Used mostly for debugging
	 * purposes.
	 */
	protected int m_threadsRequested = 0;

	/**
	 * Total number of threads granted. Used mostly for debugging
	 * purposes.
	 */
	protected int m_threadsGranted = 0;

	/**
	 * Creates a new thread manager
	 */
	public ThreadManager()
	{
		super();
		m_threads = new HashSet<ManagedThread>();
		m_threadsLock = new ReentrantLock();
	}

	/**
	 * Creates a new thread manager
	 * @param max_threads The maximum number of threads this manager
	 * is allowed to keep at any moment. Set to 0 or a negative value
	 * to mean no limit
	 */
	public ThreadManager(int max_threads)
	{
		this();
		m_maxThreads = max_threads;
	}

	/**
	 * Gets a new instance of managed thread. This method is blocking,
	 * i.e. if the manager already has the maximum number of threads
	 * allowed, it waits until a new thread can be created.
	 * @param runnable The runnable to put into the new thread
	 * @return A new thread
	 */
	public ManagedThread waitForNewThread(Runnable runnable)
	{
		while (true)
		{
			if (!m_run)
			{
				// If the manager is not started, take the opportunity of
				// this call to do a cleanup pass on the managed threads
				// (since they are not cleaned periodically by the run() method)
				cleanThreads();
			}
			m_threadsLock.lock();
			if (m_maxThreads < 0 || m_threads.size() < m_maxThreads)
			{
				ManagedThread new_thread = new ManagedThread(runnable);
				m_threads.add(new_thread);
				m_threadsLock.unlock();
				return new_thread;
			}
			sleep(s_sleepInterval);
		}
	}

	/**
	 * Attempts to get a new instance of managed thread. This method
	 * is non-blocking: if the manager already has the maximum number of
	 * threads allowed, it returns null.
	 * @param r The runnable to put into the new thread
	 * @return A new thread, or null
	 */
	public ManagedThread tryNewThread(Runnable r)
	{
		m_threadsRequested++;
		if (!m_run)
		{
			// If the manager is not started, take the opportunity of
			// this call to do a cleanup pass on the managed threads
			// (since they are not cleaned periodically by the run() method)
			cleanThreads();
		}
		ManagedThread new_thread = null;
		m_threadsLock.lock();
		if (m_maxThreads < 0 || m_threads.size() < m_maxThreads)
		{
			m_threadsGranted++;
			new_thread = new ManagedThread(r);
			m_threads.add(new_thread);
		}
		m_threadsLock.unlock();
		return new_thread;
	}

	@Override
	public String toString()
	{
		return m_threads.toString();
	}

	/**
	 * Tells the default manager to allow threads
	 */
	public static void allowThreads()
	{
		defaultManager.m_maxThreads = -1;
	}

	/**
	 * Causes the current thread to sleeps for some time
	 * @param duration The duration in milliseconds
	 */
	public static void sleep(long duration)
	{
		try
		{
			Thread.sleep(duration);
		}
		catch (InterruptedException e)
		{
			Thread.currentThread().interrupt();
		}
	}

	/**
	 * A thread managed by a thread manager. This differs from a plain
	 * Java thread by the possibility to mark it as "disposable", meaning
	 * that its consumer has finished using it.
	 */
	public static class ManagedThread extends Thread
	{
		/**
		 * Whether this thread is disposable
		 */
		private boolean m_disposable = false;

		/**
		 * Creates a new managed thread. Note that this constructor has
		 * a reduced visibility, as one is expected to pass through the
		 * thread manager to get an instance of such a thread.
		 */
		protected ManagedThread()
		{
			super();
		}

		/**
		 * Creates a managed thread from a runnable
		 * @param r The runnable
		 */
		protected ManagedThread(Runnable r)
		{
			super(r);
		}

		/**
		 * Creates a managed thread from another thread
		 * @param t The thread
		 */
		protected ManagedThread(Thread t)
		{
			super(t);
		}

		/**
		 * Checks if this thread is disposable
		 * @return true if disposable, false otherwise
		 */
		public final boolean isDisposable()
		{
			return m_disposable;
		}

		/**
		 * Marks this thread as disposable
		 */
		public final void dispose()
		{
			m_disposable = true;
		}

		@Override
		public String toString()
		{
			return super.toString() + ":" + m_disposable;
		}
		
		@Override
		public void run()
		{
			super.run();
		}
	}

	@Override
	public void run()
	{
		// Periodically clean threads
		while (m_run)
		{
			cleanThreads();
			sleep(s_sleepInterval);
		}

	}

	/**
	 * Stops the thread manager
	 */
	public void stop()
	{
		m_run = false;
	}

	/**
	 * Deletes any thread that is marked as disposable
	 */
	protected void cleanThreads()
	{
		m_threadsLock.lock();
		Iterator<ManagedThread> thread_it = m_threads.iterator();
		while (thread_it.hasNext())
		{
			ManagedThread mt = thread_it.next();
			if (mt.m_disposable)
			{
				thread_it.remove();
			}
		}
		m_threadsLock.unlock();
	}

	/**
	 * Gets the number of threads that have been requested from this
	 * manager, so far.
	 * @return The number of threads
	 */
	public int getNumThreadsRequested()
	{
		return m_threadsRequested;
	}

	/**
	 * Gets the number of threads that have been granted from this
	 * manager, so far.
	 * @return The number of threads
	 */
	public int getNumThreadsGranted()
	{
		return m_threadsGranted;
	}

}
