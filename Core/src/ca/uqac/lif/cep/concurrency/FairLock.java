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

import java.util.ArrayList;
import java.util.List;

/**
 * Implementation of a fair lock. The fair lock keeps in a queue
 * all the threads that asked for the lock, and gives them the lock
 * in in the order they asked. This enforces some liveness to the
 * execution of threads, as a thread that asks for the lock is guaranteed
 * not to starve (provided the threads before it release the lock eventually).
 * <p>
 * @see <a href="http://tutorials.jenkov.com/java-concurrency/starvation-and-fairness.html">Starvation and Fairness</a>
 */
public class FairLock
{
	private boolean isLocked = false;
	private Thread lockingThread  = null;
	private List<QueueObject> waitingThreads = new ArrayList<QueueObject>();

	/**
	 * Tries to acquire a lock, but does not throw an exception
	 * @see #lock()
	 * @param b Dummy variable
	 */
	public void lock(boolean b)
	{
		try
		{
			lock();
		}
		catch (InterruptedException e)
		{
			Thread.currentThread().interrupt();
		}
	}

	/**
	 * Tries to acquire a lock
	 * @throws InterruptedException
	 */
	public void lock() throws InterruptedException
	{
		QueueObject queueObject = new QueueObject();
		boolean isLockedForThisThread = true;
		synchronized (this)
		{
			waitingThreads.add(queueObject);
		}
		while (isLockedForThisThread)
		{
			synchronized (this)
			{
				isLockedForThisThread = isLocked || waitingThreads.get(0) != queueObject;
				if (!isLockedForThisThread)
				{
					isLocked = true;
					waitingThreads.remove(queueObject);
					lockingThread = Thread.currentThread();
					return;
				}
			}
			try
			{
				queueObject.doWait();
			}
			catch (InterruptedException e)
			{
				synchronized (this)
				{
					waitingThreads.remove(queueObject);
				}
				throw e;
			}
		}
	}

	/**
	 * Releases the lock
	 */
	public synchronized void unlock()
	{
		if (this.lockingThread != Thread.currentThread())
		{
			throw new IllegalMonitorStateException("Calling thread has not locked this lock");
		}
		isLocked = false;
		lockingThread = null;
		if (waitingThreads.size() > 0)
		{
			waitingThreads.get(0).doNotify();
		}
	}

	private static class QueueObject
	{
		private boolean isNotified = false;

		public synchronized void doWait() throws InterruptedException
		{
			while (!isNotified)
			{
				this.wait();
			}
			this.isNotified = false;
		}

		public synchronized void doNotify()
		{
			this.isNotified = true;
			this.notify();
		}

		@Override
		public boolean equals(Object o)
		{
			return this == o;
		}
	}
}