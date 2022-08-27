/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2019 Sylvain Hallé

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
package ca.uqac.lif.cep.util;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SynchronousProcessor;
import ca.uqac.lif.cep.UniformProcessor;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * A container object for functions and processors applying to lists.
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class Lists
{
  private Lists()
  {
    // Utility class
  }
  
  /**
   * Processor that updates a list
   * @since 0.10.2
   */
  protected abstract static class ListUpdateProcessor extends UniformProcessor
  {
    /**
     * The underlying list
     */
    protected List<Object> m_list;

    /**
     * Create a new instance of the processor
     */
    public ListUpdateProcessor()
    {
      super(1, 1);
      m_list = new ArrayList<Object>();
    }

    @Override
    public void reset()
    {
      super.reset();
      m_list.clear();
    }

    @Override
    public Class<?> getOutputType(int index)
    {
      return List.class;
    }
  }
  
  /**
   * Updates a list.
   * @since 0.10.2
   */
  public static class PutInto extends ListUpdateProcessor
  {
    /**
     * Create a new instance of the processor
     */
    public PutInto()
    {
      super();
    }

    @Override
    public PutInto duplicate(boolean with_state)
    {
      PutInto pi = new PutInto();
      if (with_state)
      {
        pi.m_list.addAll(m_list);
      }
      return pi;
    }

    @Override
    protected boolean compute(Object[] inputs, Object[] outputs)
    {
      m_list.add(inputs[0]);
      outputs[0] = m_list;
      return true;
    }
  }

  /**
   * Updates a list.
   * @since 0.10.2
   */
  public static class PutIntoNew extends ListUpdateProcessor
  {
    /**
     * Create a new instance of the processor
     */
    public PutIntoNew()
    {
      super();
    }

    @Override
    public PutIntoNew duplicate(boolean with_state)
    {
      PutIntoNew pi = new PutIntoNew();
      if (with_state)
      {
        pi.m_list.addAll(m_list);
      }
      return pi;
    }

    @Override
    protected boolean compute(Object[] inputs, Object[] outputs)
    {
      m_list.add(inputs[0]);
      ArrayList<Object> new_set = new ArrayList<Object>();
      new_set.addAll(m_list);
      outputs[0] = new_set;
      return true;
    }
  }

  /**
   * Common ancestor to {@link TimePack} and {@link Pack}.
   * @since 0.7
   */
  protected abstract static class AbstractPack extends SynchronousProcessor
  {
    /**
     * The list of events accumulated since the last output
     */
    protected List<Object> m_packedEvents;

    /**
     * A lock to access the list of objects
     */
    protected Lock m_lock;

    public AbstractPack(int in_arity, int out_arity)
    {
      super(in_arity, out_arity);
      m_lock = new ReentrantLock();
      m_packedEvents = newList();
    }

    /**
     * Gets a new empty list of objects
     * 
     * @return The list
     */
    protected List<Object> newList()
    {
      return new LinkedList<Object>();
    }
    
    @Override
    protected boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException
    {
      if (m_packedEvents.isEmpty())
      {
        return false;
      }
      outputs.add(new Object[] {m_packedEvents});
      return true;
    }
  }

  /**
   * Accumulates events from a first input pipe, and sends them in a burst into a
   * list based on the Boolean value received on its second input pipe. A value of
   * <tt>true</tt> triggers the output of a list, while a value of <tt>false</tt>
   * accumulates the event into the existing list.
   * <p>
   * This processor is represented graphically as follows:
   * <p>
   * <a href="{@docRoot}/doc-files/util/Pack.png"><img src="
   * {@docRoot}/doc-files/util/Pack.png" alt="Processor graph"></a>
   * 
   * @author Sylvain Hallé
   * @since 0.7
   */
  public static class Pack extends AbstractPack
  {
    /**
     * Creates a new Pack processor
     */
    public Pack()
    {
      super(2, 1);
    }

    @Override
    public Pack duplicate(boolean with_state)
    {
      Pack p = new Pack();
      if (with_state)
      {
        p.m_packedEvents.addAll(m_packedEvents);
      }
      return p;
    }

    @Override
    protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
    {
      if ((Boolean) inputs[1])
      {
        outputs.add(new Object[] { m_packedEvents });
        m_packedEvents = newList();
      }
      m_packedEvents.add(inputs[0]);
      return true;
    }
  }

  /**
   * Accumulates events that are being pushed, and sends them in a burst into a
   * list at predefined time intervals.
   * <p>
   * This processor only works in <strong>push</strong> mode. It is represented
   * graphically as follows:
   * <p>
   * <a href="{@docRoot}/doc-files/ListPacker.png"><img src="
   * {@docRoot}/doc-files/ListPacker.png" alt="Processor graph"></a>
   * 
   * @author Sylvain Hallé
   * @since 0.7
   */
  public static class TimePack extends AbstractPack
  {
    /**
     * The interval, in milliseconds, at which events will be pushed to the output
     */
    protected long m_outputInterval;

    /**
     * The timer that will send events at periodic interval
     */
    protected Timer m_timer;

    /**
     * The thread that will execute the timer
     */
    protected Thread m_timerThread;

    /**
     * Creates a new list packer.
     * 
     * @param interval
     *          The interval, in milliseconds, at which events will be pushed to the
     *          output
     */
    public TimePack(long interval)
    {
      super(1, 1);
      setInterval(interval);
    }

    /**
     * Creates a new list packer with a default interval of 1 second.
     */
    public TimePack()
    {
      this(1000);
    }

    /**
     * Sets the interval at which events are output
     * 
     * @param interval
     *          The interval, in milliseconds
     * @return This processor
     */
    public TimePack setInterval(long interval)
    {
      m_outputInterval = interval;
      return this;
    }

    @Override
    public void start()
    {
      m_timer = new Timer();
      m_timerThread = new Thread(m_timer);
      m_timerThread.start();
    }

    @Override
    public void stop()
    {
      m_timer.stop();
    }

    @Override
    protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
    {
      m_lock.lock();
      m_packedEvents.add(inputs[0]);
      m_lock.unlock();
      return true;
    }

    /**
     * Timer that pushes the contents of <code>m_packedEvents</code> every
     * <code>m_outputInterval</code> milliseconds.
     */
    protected class Timer implements Runnable
    {
      protected volatile boolean m_run = true;

      public void stop()
      {
        m_run = false;
      }

      @Override
      public void run()
      {
        m_run = true;
        while (m_run)
        {
          try
          {
            Thread.sleep(m_outputInterval);
          }
          catch (InterruptedException e)
          {
            // Restore interrupted state
            Thread.currentThread().interrupt();
          }
          Pushable p = getPushableOutput(0);
          m_lock.lock();
          p.push(m_packedEvents);
          m_packedEvents = new LinkedList<Object>();
          m_lock.unlock();
        }
      }
    }

    @Override
    public Pullable getPullableOutput(int position)
    {
      return new Pullable.PullNotSupported(this, position);
    }

    @Override
    public TimePack duplicate(boolean with_state)
    {
      TimePack tp = new TimePack();
      if (with_state)
      {
        tp.m_packedEvents.addAll(m_packedEvents);
      }
      return tp;
    }
  }

  /**
   * Unpacks a collection of objects by outputting its contents as separate events. This
   * processor is represented graphically as follows:
   * <p>
   * <a href="{@docRoot}/doc-files/ListUnpacker.png"><img src="
   * {@docRoot}/doc-files/ListUnpacker.png" alt="Processor graph"></a>
   * 
   * @author Sylvain Hallé
   */
  public static class Unpack extends SynchronousProcessor
  {
    /**
     * Creates a new list unpacker
     */
    public Unpack()
    {
      super(1, 1);
    }

    @Override
    protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
    {
      if (inputs[0].getClass().isArray())
      {
        Object[] list = (Object[]) inputs[0];
        for (Object o : list)
        {
          outputs.add(new Object[] { o });
        }
      }
      else
      {
        @SuppressWarnings("unchecked")
        Collection<Object> list = (Collection<Object>) inputs[0];
        for (Object o : list)
        {
          outputs.add(new Object[] { o });
        }
      }
      return true;
    }

    @Override
    public Unpack duplicate(boolean with_state)
    {
      Unpack up = new Unpack();
      if (with_state)
      {
        up.m_outputQueues[0].addAll(m_outputQueues[0]);
      }
      return up;
    }
  }
  
  /**
   * A list that implements equality. Two math lists are considered equal if
   * they have equal size and elements at corresponding indices are equal.
   * @param <T> The type of elements in the list
   */
  public static class MathList<T> extends ArrayList<T>
  {
		/**
		 * Dummy UID.
		 */
		private static final long serialVersionUID = 1L;
		
		/**
		 * Creates a new math list and adds elements from an array.
		 * @param elements The elements to add
		 */
		@SafeVarargs
		public MathList(T ... elements)
		{
			super(elements.length);
			for (T t : elements)
			{
				add(t);
			}
		}
  	
		@Override
		public int hashCode()
		{
			int h = 0;
			for (T t : this)
			{
				if (t != null)
				{
					h += t.hashCode();
				}
			}
			return h;
		}
		
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object o)
		{
			if (!(o instanceof MathList))
			{
				return false;
			}
			MathList<T> l = (MathList<T>) o;
			if (l.size() != size())
			{
				return false;
			}
			for (int i = 0; i < size(); i++)
			{
				if (!Equals.isEqualTo(get(i), l.get(i)))
				{
					return false;
				}
			}
			return true;
		}
  }
}
