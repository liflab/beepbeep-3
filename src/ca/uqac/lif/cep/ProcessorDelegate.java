/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2026 Sylvain Hallé

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
package ca.uqac.lif.cep;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Queue;

import ca.uqac.lif.petitpoucet.CompositePart;
import ca.uqac.lif.petitpoucet.Part;
import ca.uqac.lif.petitpoucet.Explainable.ExplanationException;
import ca.uqac.lif.petitpoucet.circuit.Connectable.OutputPart;

class ProcessorDelegate
{
	protected final Processor m_pupil;
	
	/**
	 * An array of input event queues. This is where the input events will be stored
	 * before the processor consumes them. There are as many input queues as the
	 * input arity of the processor.
	 */
	protected Queue<Object>[] m_inputQueues;

	/**
	 * An array of output event queues. This is where the output events will be
	 * stored when the processor does its computation. There are as many output
	 * queues as the output arity of the processor.
	 */
	protected Queue<Object>[] m_outputQueues;

	/**
	 * A static counter, to be incremented every time a new {@link Processor} is
	 * instantiated. This is used to give a unique integer number to every
	 * processor.
	 */
	private static int s_uniqueIdCounter = 0;

	/**
	 * The unique ID given to this processor instance
	 */
	private final int m_uniqueId;

	/**
	 * The context in which the processor is instantiated
	 */
	protected Context m_context = null;
	
	/**
	 * Indicates whether the processor has been notified of the end of trace or
	 * not. Each input pushable has its own flag, and the end of trace signal
	 * is propagated only once all upstream processors have sent the
	 * notification.
	 */
	protected boolean[] m_hasBeenNotifiedOfEndOfTrace;

	/**
	 * Indicates whether the processor has notified the end of the trace to the
	 * downstream processors it is connected to. The end of trace signal should
	 * be sent at most once.
	 */
	protected boolean m_notifiedEndOfTraceDownstream;

	
	@SuppressWarnings("unchecked")
	public ProcessorDelegate(int in_arity, int out_arity, Processor pupil)
	{
		super();
		m_pupil = pupil;
		m_uniqueId = s_uniqueIdCounter++;
		m_inputQueues = new Queue[in_arity];
		m_hasBeenNotifiedOfEndOfTrace = new boolean[in_arity];
		for (int i = 0; i < in_arity; i++)
		{
			m_inputQueues[i] = new ArrayDeque<Object>();
			m_hasBeenNotifiedOfEndOfTrace[i] = false;
		}
		m_outputQueues = new Queue[out_arity];
		for (int i = 0; i < out_arity; i++)
		{
			m_outputQueues[i] = new ArrayDeque<Object>();
		}
		m_notifiedEndOfTraceDownstream = false;
	}
	
	public void addToInputQueue(int index, Collection<?> c)
	{
		m_inputQueues[index].addAll(c);
	}
	
	public void addToOutputQueue(int index, Collection<?> c)
	{
		m_outputQueues[index].addAll(c);
	}
	
	protected boolean allNotifiedEndOfTrace()
	{
		for (int i = 0; i < m_hasBeenNotifiedOfEndOfTrace.length; i++)
		{
			if (!m_hasBeenNotifiedOfEndOfTrace[i])
			{
				return false;
			}
		}
		return true;
	}
	
	public /*@ null @*/ Object getContext(/*@ non_null @*/ String key)
	{
		if (m_context == null || !m_context.containsKey(key))
		{
			return null;
		}
		return m_context.get(key);
	}
	
	public /*@ non_null @*/ Context getContext()
	{
		// As the context map is created only on demand, we must first
		// check if a map already exists and create it if not
		if (m_context == null)
		{
			m_context = m_pupil.newContext();
		}
		return m_context;
	}
	
	public void setContext(/*@ non_null @*/ String key, Object value)
	{
		// As the context map is created only on demand, we must first
		// check if a map already exists and create it if not
		if (m_context == null)
		{
			m_context = m_pupil.newContext();
		}
		m_context.put(key, value);
	}
	
	public void setContext(/*@ null @*/ Context context)
	{
		// As the context map is created only on demand, we must first
		// check if a map already exists and create it if not
		if (context != null)
		{
			if (m_context == null)
			{
				m_context = m_pupil.newContext();
			}
			m_context.putAll(context);
		}
	}
	
	public int getUniqueId()
	{
		return m_uniqueId;
	}
	
	protected long checkPart(Part p) throws ExplanationException
  {
  	Part head = CompositePart.head(p);
  	if (!(head instanceof OutputPart))
  	{
  		throw new ExplanationException("Expected an output part");
  	}
  	OutputPart op = (OutputPart) head;
  	if (op.getIndex() < 0 || op.getIndex() >= m_outputQueues.length)
  	{
  		throw new ExplanationException("Output index out of bounds");
  	}
  	Part pos = CompositePart.head(CompositePart.tail(p));
  	if (!(pos instanceof EventAt))
  	{
  		throw new ExplanationException("Expected an event index");
  	}
  	EventAt ea = (EventAt) pos;
  	return ea.getPosition();
  }
	
	public void reset()
	{
		// Reset input
		for (int i = 0; i < m_inputQueues.length; i++)
		{
			m_inputQueues[i].clear();
		}
		// Reset output
		for (int i = 0; i < m_outputQueues.length; i++)
		{
			m_outputQueues[i].clear();
		}
		for (int i = 0; i < m_hasBeenNotifiedOfEndOfTrace.length; i++)
		{
			m_hasBeenNotifiedOfEndOfTrace[i] = false; 
		}
		m_notifiedEndOfTraceDownstream = false;
	}
	
	/*@ pure @*/ public void copyInputQueue(int index, Collection<Object> to)
	{
		to.addAll(m_inputQueues[index]);
	}
	
	/*@ pure @*/ public void copyOutputQueue(int index, Collection<Object> to)
	{
		to.addAll(m_outputQueues[index]);
	}
	
	/*@ non_null @*/ public static Queue<Object[]> getEmptyQueue()
	{
		return new ArrayDeque<Object[]>();
	}
	
	public Queue<Object> getInputQueue(int index)
	{
		Queue<Object> q = new ArrayDeque<Object>();
		q.addAll(m_inputQueues[index]);
		return q;
	}
	
	public Queue<Object> getOutputQueue(int index)
	{
		Queue<Object> q = new ArrayDeque<Object>();
		q.addAll(m_outputQueues[index]);
		return q;
	}
	
	public void duplicate(SingleProcessor p, boolean with_state)
	{
		p.setContext(m_context);
		ProcessorDelegate pd = p.delegate();
		for (int i = 0; i < m_inputQueues.length; i++)
		{
			pd.m_inputQueues[i].addAll(m_inputQueues[i]);
		}
		for (int i = 0; i < m_outputQueues.length; i++)
		{
			pd.m_outputQueues[i].addAll(m_outputQueues[i]);
		}
	}
	
	
}
