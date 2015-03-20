package ca.uqac.lif.cep;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Vector;

/**
 * Sink that accumulates events into queues
 * @author sylvain
 *
 */
public class QueueSink extends Sink
{
	protected Vector<Queue<Object>> m_queues;
	
	public QueueSink(int in_arity)
	{
		super(in_arity);
		m_queues = new Vector<Queue<Object>>();
		for (int i = 0; i < in_arity; i++)
		{
			m_queues.add(new LinkedList<Object>());
		}
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		for (int i = 0; i < m_queues.size(); i++)
		{
			Queue<Object> q = m_queues.get(i);
			q.add(inputs.get(i));
		}
		return new Vector<Object>();
	}
	
	public Queue<Object> getQueue(int i)
	{
		return m_queues.get(i);
	}

}
