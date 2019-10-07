package ca.uqac.lif.cep;

import java.util.AbstractQueue;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.ProcessorQueryable.QueryableCircuitConnection;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;
import ca.uqac.lif.petitpoucet.circuit.CircuitQueryable;

public abstract class SingleProcessor implements Processor
{
	/*@ non_null @*/ protected AbstractQueue<Object>[] m_inputQueues;

	/*@ non_null @*/ protected AbstractQueue<Object>[] m_outputQueues;

	/*@ non_null @*/ protected Pullable[] m_inputPullables;

	/*@ non_null @*/ protected Pushable[] m_inputPushables;

	/*@ non_null @*/ protected Pushable[] m_outputPushables;

	/*@ non_null @*/ protected Pullable[] m_outputPullables;

	/*@ non_null @*/ protected Context m_context;
	
	/*@ nullable @*/ protected ProcessorQueryable m_queryable;

	protected boolean m_hasMore;

	protected boolean m_endReceived;

	protected int m_endCounter;

	public static final transient String s_contentsKey = "contents";

	public static final transient String s_inputQueuesKey = "inqueues";

	public static final transient String s_outputQueuesKey = "outqueues";

	public static final transient String s_contextKey = "context";
	
	public static final transient String s_queryableKey = "queryable";

	//@ requires in_arity >= 0;
	//@ requires out_arity >= 0;
	@SuppressWarnings("unchecked")
	public SingleProcessor(int in_arity, int out_arity)
	{
		super();
		m_inputQueues = new AbstractQueue[in_arity];
		m_inputPullables = new Pullable[in_arity];
		m_inputPushables = new Pushable[in_arity];
		m_context = new Context();
		m_hasMore = true;
		m_endReceived = false;
		m_endCounter = 0;
		for (int i = 0; i < in_arity; i++)
		{
			m_inputQueues[i] = new ConcurrentLinkedQueue<Object>();
		}
		m_outputQueues = new AbstractQueue[out_arity];
		m_outputPushables = new Pushable[out_arity];
		m_outputPullables = new Pullable[out_arity];
		for (int i = 0; i < out_arity; i++)
		{
			m_outputQueues[i] = new ConcurrentLinkedQueue<Object>();
		}
		m_queryable = null;
	}

	@Override
	public Pushable getPushableInput(int index)
	{
		try
		{
			if (m_inputPushables[index] == null)
			{
				if (m_inputPushables.length == 1)
				{
					m_inputPushables[index] = new UnaryPushable(index);
				}
				else
				{
					m_inputPushables[index] = new SinglePushable(index);
				}
			}
			return m_inputPushables[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public final Pushable getPushableInput()
	{
		return getPushableInput(0);
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		try
		{
			if (m_outputPullables[index] == null)
			{
				// Yes, we really mean *input*Pullables below. The special
				// behavior depends on the fact that the processor has an *input*
				// arity of 1
				if (m_inputPullables.length == 1)
				{
					m_outputPullables[index] = new UnaryPullable(index);
				}
				else
				{
					m_outputPullables[index] = new SinglePullable(index);
				}
			}
			return m_outputPullables[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public final Pullable getPullableOutput()
	{
		return getPullableOutput(0);
	}

	@Override
	public int getInputArity()
	{
		return m_inputQueues.length;
	}

	@Override
	public int getOutputArity() 
	{
		return m_outputQueues.length;
	}

	@Override
	public void start()
	{
		// Do nothing
	}

	@Override
	public void stop()
	{
		// Do nothing
	}

	@Override
	public void setPullableInput(int index, Pullable p)
	{
		try
		{
			m_inputPullables[index] = p;
			QueryableCircuitConnection cc = new QueryableCircuitConnection(p.getIndex(), (CircuitQueryable) p.getObject().getQueryable());
			m_queryable.setToInput(index, cc);
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public void setToInput(int index, CircuitConnection c)
	{
		setPullableInput(index, (Pullable) c);
	}

	@Override
	public void setPushableOutput(int index, Pushable p)
	{
		try
		{
			m_outputPushables[index] = p;
			QueryableCircuitConnection cc = new QueryableCircuitConnection(p.getIndex(), (CircuitQueryable) p.getObject().getQueryable());
			m_queryable.setToOutput(index, cc);
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public void setToOutput(int index, CircuitConnection c)
	{
		setPushableOutput(index, (Pushable) c);
	}

	protected class SinglePullable implements Pullable
	{
		protected int m_index;
		
		//@ requires index >= 0;
		public SinglePullable(int index)
		{
			super();
			m_index = index;
		}

		protected void handlePull()
		{
			if (!m_hasMore)
			{
				return;
			}
			while (m_hasMore)
			{
				Object[] inputs = new Object[m_inputPullables.length];
				Queue<Object[]> outputs = new ArrayDeque<Object[]>();
				for (int i = 0; i < m_inputPullables.length; i++)
				{
					if (!m_inputPullables[i].hasNext())
					{
						m_hasMore = false;
						return;
					}
					inputs[i] = m_inputPullables[i].pull();
				}
				m_hasMore = compute(inputs, outputs);
				if (outputs.isEmpty())
				{
					continue;
				}
				while (!outputs.isEmpty())
				{
					Object[] front = outputs.remove();
					for (int i = 0; i < m_outputQueues.length; i++)
					{
						m_outputQueues[i].add(front[i]);
					}
				}
				return;
			}
		}

		@Override
		public Object pull()
		{
			if (m_outputQueues[m_index].isEmpty())
			{
				handlePull();
			}
			try
			{
				return m_outputQueues[m_index].remove();
			}
			catch (NoSuchElementException e)
			{
				throw new ProcessorException(e);
			}
		}

		@Override
		public boolean hasNext()
		{
			if (m_outputQueues[m_index].isEmpty())
			{
				handlePull();
			}
			return !m_outputQueues[m_index].isEmpty();
		}

		@Override
		public final Object next()
		{
			return pull();
		}

		@Override
		public void reset()
		{
			// Do nothing
		}

		@Override
		/*@ pure nullable @*/ public Class<?> getType()
		{
			return getOutputType(m_index);
		}

		@Override
		public NextStatus hasNextSoft()
		{
			if (hasNext())
			{
				return NextStatus.YES;
			}
			return NextStatus.NO;
		}

		@Override
		public Object pullSoft() 
		{
			return pull();
		}

		@Override
		public int getIndex() 
		{
			return m_index;
		}

		@Override
		public Processor getObject() 
		{
			return SingleProcessor.this;
		}
	}

	protected class SinglePushable implements Pushable
	{
		protected int m_index;

		public SinglePushable(int index)
		{
			super();
			m_index = index;
		}

		@Override
		public void push(Object o)
		{
			if (!m_hasMore)
			{
				return;
			}
			m_inputQueues[m_index].add(o);
			for (int i = 0; i < m_inputQueues.length; i++)
			{
				if (m_inputQueues[i].isEmpty())
				{
					return;
				}
			}
			Object[] inputs = new Object[m_inputQueues.length];
			for (int i = 0; i < m_inputQueues.length; i++)
			{
				inputs[i] = m_inputQueues[i].remove();
			}
			if (m_endReceived)
			{
				m_endCounter--;
			}
			Queue<Object[]> outputs = new ArrayDeque<Object[]>();
			m_hasMore = compute(inputs, outputs);
			while (!outputs.isEmpty())
			{
				Object[] front = outputs.remove();
				for (int i = 0; i < m_outputPushables.length; i++)
				{
					m_outputPushables[i].push(front[i]);
				}
			}
			if (!m_hasMore)
			{
				// If the processor says no more events will ever be produced,
				// then we can clear the input queues of any event left
				for (int i = 0; i < m_inputQueues.length; i++)
				{
					m_inputQueues[i].clear();
				}
				// Tell the pushables downstream that this is the end
				for (Pushable p : m_outputPushables)
				{
					p.end();
				}
			}
			else if (m_endReceived && m_endCounter == 0)
			{
				// We reached the end of the buffer for a pushable that
				// told us no more event would be coming
				end();
				m_hasMore = false;
			}
		}

		@Override
		public void end()
		{
			if (!m_hasMore)
			{
				// hasMore is a flag used in push mode to remember if
				// onEnd has already been called
				return;
			}
			if (!m_endReceived)
			{
				m_endReceived = true;
				m_endCounter = m_inputQueues[m_index].size();
			}
			else
			{
				m_endCounter = Math.min(m_endCounter, m_inputQueues[m_index].size());
			}
			if (m_endCounter == 0)
			{
				Queue<Object[]> outputs = new ArrayDeque<Object[]>();
				onEnd(outputs);
				m_hasMore = false;
				while (!outputs.isEmpty())
				{
					Object[] front = outputs.remove();
					for (int i = 0; i < m_outputPushables.length; i++)
					{
						m_outputPushables[i].push(front[i]);
					}
				}
				for (int i = 0; i < m_outputPushables.length; i++)
				{
					m_outputPushables[i].end();
				}
			}
		}

		@Override
		public void reset()
		{
			// Do nothing
		}

		@Override
		/*@ pure nullable @*/ public Class<?> getType() 
		{
			return getInputType(m_index);
		}

		@Override
		public int getIndex() 
		{
			return m_index;
		}

		@Override
		public Processor getObject() 
		{
			return SingleProcessor.this;
		}
	}

	@Override
	public void reset()
	{
		// Clear queues
		for (int i = 0; i < m_inputQueues.length; i++)
		{
			m_inputQueues[i].clear();
		}
		for (int i = 0; i < m_outputQueues.length; i++)
		{
			m_outputQueues[i].clear();
		}
		m_hasMore = true;
		m_endReceived = false;
		m_endCounter = 0;
		m_queryable = getQueryable(m_inputQueues.length, m_outputQueues.length);
	}

	@Override
	public Object getContext(String key)
	{
		return m_context.getOrDefault(key, null);
	}

	@Override
	public void setContext(String key, Object value)
	{
		m_context.put(key, value);
	}

	@Override
	public final SingleProcessor duplicate()
	{
		return (SingleProcessor) duplicate(false);
	}

	/*@ pure @*/ protected SingleProcessor copyInto(/*@ non_null @*/ SingleProcessor p, boolean with_state)
	{
		p.m_queryable = m_queryable.duplicate(with_state);
		if (with_state)
		{
			p.m_context.putAll(m_context);
			for (int i = 0; i < m_inputQueues.length; i++)
			{
				p.m_inputQueues[i].addAll(m_inputQueues[i]);
			}			
			for (int i = 0; i < m_outputQueues.length; i++)
			{
				p.m_outputQueues[i].addAll(m_outputQueues[i]);
			}
		}
		return p;
	}

	/*@ pure nullable @*/
	@Override
	public Pullable getInputConnection(int index)
	{
		try
		{
			return m_inputPullables[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	/*@ pure nullable @*/
	@Override
	public Pushable getOutputConnection(int index)
	{
		try
		{
			return m_outputPushables[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	protected abstract boolean compute(Object[] inputs, Queue<Object[]> outputs);

	public void onEnd(Queue<Object[]> outputs)
	{
		// By default, do nothing
	}

	/*@ pure @*/ protected Class<?> getInputType(int index)
	{
		return Object.class;
	}

	/*@ pure @*/ protected Class<?> getOutputType(int index)
	{
		return Object.class;
	}
	
	@Override
	/*@ non_null @*/ public final Queryable getQueryable()
	{
		if (m_queryable == null)
		{
			m_queryable = getQueryable(m_inputQueues.length, m_outputQueues.length);
		}
		return m_queryable;
	}

	@Override
	/*@ pure @*/ public final Object print(ObjectPrinter<?> printer) throws PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		List<Queue<Object>> in_queues = new ArrayList<Queue<Object>>(m_inputQueues.length); 
		for (int i = 0; i < m_inputQueues.length; i++)
		{
			in_queues.add(m_inputQueues[i]);
		}
		map.put(s_inputQueuesKey, in_queues);
		List<Queue<Object>> out_queues = new ArrayList<Queue<Object>>(m_outputQueues.length);
		for (int i = 0; i < m_outputQueues.length; i++)
		{
			out_queues.add(m_outputQueues[i]);
		}
		map.put(s_outputQueuesKey, out_queues);
		map.put(s_contextKey, m_context);
		Object state = printState();
		if (state != null)
		{
			map.put(s_contentsKey, state);
		}
		map.put(s_contextKey, m_context);
		map.put(s_queryableKey, m_queryable);
		return printer.print(map);
	}

	@Override
	/*@ non_null @*/ public final SingleProcessor read(ObjectReader<?> reader, Object o) throws ReadException
	{
		Object r_o = reader.read(o);
		if (!(r_o instanceof Map))
		{
			throw new ReadException("This processor expects a deserialized map");
		}
		Map<?,?> map = (Map<?,?>) r_o;
		if (!map.containsKey(s_inputQueuesKey) || !map.containsKey(s_outputQueuesKey))
		{
			throw new ReadException("Invalid map format");
		}
		Object o_iq = map.get(s_inputQueuesKey);
		if (o_iq == null || !(o_iq instanceof List))
		{
			throw new ReadException("Invalid format for input queues");
		}
		List<?> in_q = (List<?>) o_iq;
		Object o_oq = map.get(s_outputQueuesKey);
		if (o_oq == null || !(o_oq instanceof List))
		{
			throw new ReadException("Invalid format for output queues");
		}
		List<?> out_q = (List<?>) o_oq;
		Object state = map.getOrDefault(s_contentsKey, null);
		SingleProcessor new_p = readState(state, in_q.size(), out_q.size());
		for (int i = 0; i < in_q.size(); i++)
		{
			Object q_r = in_q.get(i);
			if (q_r == null || !(q_r instanceof Queue))
			{
				throw new ReadException("Invalid format for input queue " + i);
			}
			new_p.m_inputQueues[i].addAll((Queue<?>) q_r);
		}
		for (int i = 0; i < out_q.size(); i++)
		{
			Object q_r = out_q.get(i);
			if (q_r == null || !(q_r instanceof Queue))
			{
				throw new ReadException("Invalid format for output queue " + i);
			}
			new_p.m_outputQueues[i].addAll((Queue<?>) q_r);
		}
		Object o_context = map.getOrDefault(s_contextKey, null);
		if (o_context != null && o_context instanceof Context)
		{
			new_p.m_context.putAll((Context) o_context);
		}
		else
		{
			throw new ReadException("Invalid format for context");
		}
		Object q_oq = map.getOrDefault(s_queryableKey, null);
		if (q_oq == null || !(q_oq instanceof ProcessorQueryable))
		{
			throw new ReadException("Invalid format for queryable");
		}
		ProcessorQueryable queryable = (ProcessorQueryable) q_oq;
		new_p.m_queryable = queryable;
		return new_p;
	}

	protected class UnaryPushable extends SinglePushable
	{
		public UnaryPushable(int index)
		{
			super(index);
		}

		@Override
		public void push(Object o)
		{
			if (!m_hasMore)
			{
				return;
			}
			Queue<Object[]> outputs = new ArrayDeque<Object[]>();
			m_hasMore = compute(new Object[] {o}, outputs);
			while (!outputs.isEmpty())
			{
				Object[] front = outputs.remove();
				for (int i = 0; i < m_outputPushables.length; i++)
				{
					m_outputPushables[i].push(front[i]);
				}
			}
			if (!m_hasMore)
			{
				// hasMore has just turned false: tell the pushables
				// downstream that this is the end
				for (Pushable p : m_outputPushables)
				{
					p.end();
				}
			}
		}
		
		@Override
		public void end()
		{
			if (!m_hasMore)
			{
				return;
			}
			Queue<Object[]> outputs = new ArrayDeque<Object[]>();
			onEnd(outputs);
			m_hasMore = false;
			while (!outputs.isEmpty())
			{
				Object[] front = outputs.remove();
				for (int i = 0; i < m_outputPushables.length; i++)
				{
					m_outputPushables[i].push(front[i]);
				}
			}
			for (int i = 0; i < m_outputPushables.length; i++)
			{
				m_outputPushables[i].end();
			}
		}
	}
	
	@Override
	public String toString()
	{
		return getClass().getSimpleName() + "@" + System.identityHashCode(this); 
	}

	protected class UnaryPullable extends SinglePullable
	{
		public UnaryPullable(int index)
		{
			super(index);
		}

		@Override
		protected void handlePull()
		{
			// TODO: eventually, optimize for processor with single input
			super.handlePull();
		}
	}

	/*@ pure non_null @*/ protected abstract SingleProcessor readState(/*@ nullable @*/ Object state, int in_arity, int out_arity) throws ReadException;

	/*@ pure nullable @*/ protected abstract Object printState();
	
	/*@ non_null @*/ protected ProcessorQueryable getQueryable(int in_arity, int out_arity)
	{
		return new ProcessorQueryable(SingleProcessor.this.toString(), in_arity, out_arity);
	}
}