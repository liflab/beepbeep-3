package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.ProcessorQueryable;

public class QueueSink extends Sink
{
	/*@ non_null @*/ protected Queue<Object[]> m_queue;
	
	public QueueSink(int arity)
	{
		super(arity);
		m_queue = new ArrayDeque<Object[]>();
		m_queryable = new ProcessorQueryable(toString(), arity, 0);
	}
	
	public QueueSink()
	{
		this(1);
	}

	@Override
	public QueueSink duplicate(boolean with_state)
	{
		QueueSink qs = new QueueSink(m_inputQueues.length);
		if (with_state)
		{
			qs.m_queue.addAll(m_queue);
		}
		return qs;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
	{
		m_queue.add(inputs);
		return true;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected QueueSink readState(Object state, int in_arity, int out_arity) throws ReadException
	{
		if (state == null || !(state instanceof List))
		{
			throw new ReadException("Unexpected list format");
		}
		try
		{
			QueueSink qs = new QueueSink(in_arity);
			List<List<Object>> queue = (List<List<Object>>) state;
			for (List<Object> front : queue)
			{
				Object[] a_front = front.toArray();
				if (a_front.length != in_arity)
				{
					throw new ReadException("Unexpected front size");
				}
				qs.m_queue.add(a_front);
			}
			return qs;
		}
		catch (ClassCastException cce)
		{
			throw new ReadException(cce);
		}
	}

	@Override
	protected Object printState()
	{
		List<List<Object>> queue = new ArrayList<List<Object>>(m_queue.size());
		List<Object[]> q_copy = new ArrayList<Object[]>(m_queue.size());
		q_copy.addAll(m_queue);
		for (int i = 0; i < q_copy.size(); i++)
		{
			Object[] front = q_copy.get(i);
			List<Object> l_front = new ArrayList<Object>(front.length);
			for (int j = 0; j < front.length; j++)
			{
				l_front.add(front[j]);
			}
			queue.add(l_front);
		}
		return queue;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_queue.clear();
	}
	
	/*@ pure non_null @*/ public Queue<Object[]> getQueue()
	{
		return m_queue;
	}
	
	@Override
	protected QueueSinkQueryable getQueryable(int in_arity, int out_arity)
	{
		return new QueueSinkQueryable(toString(), in_arity, out_arity);
	}
	
	public static class QueueSinkQueryable extends ProcessorQueryable
	{
		public QueueSinkQueryable(/*@ non_null @*/ String reference, int in_arity, int out_arity)
		{
			super(reference, in_arity, out_arity);
		}
		
		@Override
		public QueueSinkQueryable duplicate(boolean with_state)
		{
			return new QueueSinkQueryable(m_reference, m_inputConnections.length, m_outputConnections.length);
		}
		
		@Override
		public Object printState()
		{
			return null;
		}
		
		@Override
		public QueueSinkQueryable readState(/*@ non_null @*/ String reference, int in_arity, int out_arity, /*@ nullable @*/ Object o) throws ReadException
		{
			return new QueueSinkQueryable(reference, in_arity, out_arity);
		}
	}	
}
