package ca.uqac.lif.cep;

import java.util.Queue;
import java.util.Vector;

public class QueueSource extends Source
{
	/**
	 * The events to repeat endlessly
	 */
	protected final Vector<Object> m_events;
	
	/**
	 * The index of the next event to produce
	 */
	protected int m_index;
	
	public QueueSource(Object o, int arity)
	{
		super(arity);
		m_events = new Vector<Object>();
		m_events.add(o);
		m_index = 0;
	}
	
	public QueueSource(Queue<Object> o, int arity)
	{
		super(arity);
		m_events = new Vector<Object>();
		m_events.addAll(o);
		m_index = 0;
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		Vector<Object> output = new Vector<Object>();
		Object event = m_events.get(m_index);
		m_index = (m_index + 1) % m_events.size();
		for (int i = 0; i < getOutputArity(); i++)
		{
			output.add(event);
		}
		return output;
	}
}
