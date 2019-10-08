package ca.uqac.lif.cep.tmf;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.common.NthOf;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.common.CollectionDesignator.NthElement;

public class QueueSource extends Source
{
	protected boolean m_loop = true;

	protected int m_index = 0;

	/*@ non_null @*/ protected List<Object[]> m_queue;
	
	public static final transient String s_loopKey = "loop";
	
	public static final transient String s_queueKey = "queue";
	
	public static final transient String s_indexKey = "index";

	public QueueSource(int out_arity)
	{
		super(out_arity);
		m_queue = new ArrayList<Object[]>();
		m_queryable = new QueueSourceQueryable(toString(), 0, out_arity, 0, m_loop);
	}

	public QueueSource()
	{
		this(1);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		try
		{
			outputs.add(m_queue.get(m_index));
			m_index++;
			if (m_loop)
			{
				m_index = m_index % m_queue.size();
			}
			return m_index < m_queue.size();
		}
		catch (IndexOutOfBoundsException e)
		{
			return false;
		}
	}

	public QueueSource add(Object ... front)
	{
		m_queue.add(front);
		((QueueSourceQueryable) m_queryable).setQueueSize(m_queue.size());
		return this;
	}

	public QueueSource setEvents(Object ... events)
	{
		for (Object e : events)
		{
			m_queue.add(new Object[] {e});
		}
		((QueueSourceQueryable) m_queryable).setQueueSize(m_queue.size());
		return this;
	}

	public QueueSource loop(boolean b)
	{
		m_loop = b;
		((QueueSourceQueryable) m_queryable).setLoop(b);
		return this;
	}

	@Override
	public void reset()
	{
		super.reset();
		m_index = 0;
	}

	@Override
	public QueueSource duplicate(boolean with_state)
	{
		QueueSource qs = new QueueSource(getOutputArity());
		return (QueueSource) copyInto(qs,  with_state);
	}

	protected SingleProcessor copyInto(SingleProcessor p, boolean with_state)
	{
		p = super.copyInto(p, with_state);
		((QueueSource) p).m_queue.addAll(m_queue);
		if (with_state)
		{
			((QueueSource) p).m_index = m_index;
		}
		return p;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected QueueSource readState(Object state, int in_arity, int out_arity) throws ReadException 
	{
		try
		{
			Map<String,Object> map = (Map<String,Object>) state;
			QueueSource src = new QueueSource();
			src.m_loop = (Boolean) map.get(s_loopKey);
			src.m_index = (Integer) map.get(s_indexKey);
			List<List<Object>> queue = (List<List<Object>>) map.get(s_queueKey);
			for (int i = 0; i < queue.size(); i++)
			{
				List<Object> l_o = queue.get(i);
				src.m_queue.add(l_o.toArray());
			}
			return src;
		}
		catch (ClassCastException e)
		{
			throw new ReadException(e);
		}
		catch (NullPointerException e)
		{
			throw new ReadException(e);
		}
	}

	@Override
	protected Object printState() 
	{
		Map<String,Object> state = new HashMap<String,Object>();
		state.put(s_loopKey, m_loop);
		state.put(s_indexKey, m_index);
		List<List<Object>> queue = new ArrayList<List<Object>>(m_queue.size());
		for (int i = 0; i < m_queue.size(); i++)
		{
			Object[] front = m_queue.get(i);
			List<Object> l_front = new ArrayList<Object>(front.length);
			for (int j = 0; j < front.length; j++)
			{
				l_front.add(front[j]);
			}
			queue.add(l_front);
		}
		state.put(s_queueKey, queue);
		return state;
	}
	
	@Override
	protected ProcessorQueryable getQueryable(int in_arity, int out_arity) 
	{
		return new QueueSourceQueryable(toString(), in_arity, out_arity, 0, m_loop);
	}
	
	protected static class QueueSourceQueryable extends ProcessorQueryable
	{
		protected int m_queueSize;
		
		protected boolean m_loop;
		
		public static final transient String s_sizeKey = "size";
		
		public QueueSourceQueryable(/*@ non_null @*/ String reference, int in_arity, int out_arity, int queue_size, boolean loop)
		{
			super(reference, in_arity, out_arity);
			m_queueSize = queue_size;
			m_loop = loop;
		}
		
		public void setQueueSize(int size)
		{
			m_queueSize = size;
		}
		
		public void setLoop(boolean b)
		{
			m_loop = b;
		}

		@Override
		public ProcessorQueryable duplicate(boolean with_state)
		{
			return new QueueSourceQueryable(m_reference, m_inputConnections.length, m_outputConnections.length, m_queueSize, m_loop);
		}
		
		@Override
		protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			Designator t_head = tail.peek();
			Designator t_tail = tail.tail();
			if (!(t_head instanceof NthEvent))
			{
				// Unknown
				return unknownLink(root, factory);
			}
			NthEvent nth = (NthEvent) t_head;
			int index = nth.getIndex();
			if (index < 0 || (!m_loop && index >= m_queueSize))
			{
				// Unknown
				return unknownLink(root, factory);
			}
			int queue_pos = index % m_queueSize;
			ComposedDesignator cd = new ComposedDesignator(t_tail, new NthOfQueue(queue_pos), new NthElement(out_index));
			TraceabilityNode node = factory.getObjectNode(cd, null);
			root.addChild(node, Quality.EXACT);
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
			leaves.add(node);
			return leaves;
		}
		
		@Override
		public Object printState()
		{
			Map<String,Object> map = new HashMap<String,Object>(2);
			map.put(s_loopKey, m_loop);
			map.put(s_sizeKey, m_queueSize);
			return map;
		}
		
		@SuppressWarnings("unchecked")
		@Override
		public QueueSourceQueryable readState(/*@ non_null @*/ String reference, int in_arity, int out_arity, /*@ nullable @*/ Object o) throws ReadException
		{
			if (o == null)
			{
				throw new ReadException("Invalid map");
			}
			try
			{
				Map<String,Object> map = (Map<String,Object>) o;
				if (!map.containsKey(s_sizeKey) || !map.containsKey(s_loopKey))
				{
					throw new ReadException("Invalid map format");
				}
				int size = (Integer) map.get(s_sizeKey);
				boolean loop = (Boolean) map.get(s_loopKey);
				return new QueueSourceQueryable(reference, in_arity, out_arity, size, loop);
			}
			catch (ClassCastException cce)
			{
				throw new ReadException(cce);
			}
		}
	}
	
	public static class NthOfQueue extends NthOf
	{
		public NthOfQueue(int index) 
		{
			super(index);
		}

		@Override
		public boolean appliesTo(Object o) 
		{
			return o instanceof Queue;
		}

		@Override
		public Designator peek() 
		{
			return this;
		}

		@Override
		public Designator tail() 
		{
			return null;
		}
		
		@Override
		public String toString()
		{
			return "Element #" + m_index + " of queue";
		}
	}
}
