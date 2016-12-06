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
 * {@link http://tutorials.jenkov.com/java-concurrency/starvation-and-fairness.html}
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
			// Do nothing
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