package ca.uqac.lif.cep.tmf;

import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.UpstreamQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.common.CollectionDesignator.NthElement;

public class SinkLast extends Sink
{
	/*@ non_null @*/ protected Object[] m_last;
	
	protected boolean m_isEmpty;
	
	public SinkLast(int arity)
	{
		super(arity);
		m_last = new Object[arity];
		m_isEmpty = true;
		m_queryable = new SinkLastQueryable(toString(), arity);
	}
	
	public SinkLast()
	{
		this(1);
	}
	
	/*@ pure @*/ public Object getLast(int index)
	{
		return m_last[index];
	}
	
	/*@ pure @*/ public Object getLast()
	{
		return getLast(0);
	}
	
	/*@ pure @*/ public boolean isEmpty()
	{
		return m_isEmpty;
	}
	
	@Override
	public SinkLastQueryable getQueryable(int in_arity, int out_arity)
	{
		return new SinkLastQueryable(toString(), in_arity);
	}

	@Override
	/*@ pure @*/ public SingleProcessor duplicate(boolean with_state)
	{
		SinkLast sl = new SinkLast(getInputArity());
		return copyInto(sl, with_state);
	}
	
	@Override
	/*@ pure @*/ public SingleProcessor copyInto(SingleProcessor p, boolean with_state)
	{
		p = super.copyInto(p, with_state);
		if (with_state)
		{
			for (int i = 0; i < m_last.length; i++)
			{
				((SinkLast) p).m_last[i] = m_last[i];
			}
			((SinkLast) p).m_isEmpty = m_isEmpty;
		}
		return p;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		m_last = inputs;
		m_isEmpty = false;
		((SinkLastQueryable) m_queryable).addCall();
		return true;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		for (int i = 0; i < m_last.length; i++)
		{
			m_last[i] = null;
		}
		m_isEmpty = true;
		((SinkLastQueryable) m_queryable).reset();
	}

	@Override
	protected SinkLast readState(Object state, int in_arity, int out_arity) throws ReadException
	{
		return new SinkLast(in_arity);
	}

	@Override
	protected Object printState() 
	{
		return null;
	}
	
	public static class SinkLastQueryable extends ProcessorQueryable
	{
		protected int m_calls;
		
		public SinkLastQueryable(/*@ non_null @*/ String reference, int in_arity)
		{
			super(reference, in_arity, 0);
			m_calls = 0;
		}
		
		public void addCall()
		{
			m_calls++;
		}
		
		public void reset()
		{
			m_calls = 0;
		}
		
		@Override
		public SinkLastQueryable duplicate(boolean with_state)
		{
			SinkLastQueryable slq = new SinkLastQueryable(m_reference, m_inputConnections.length);
			if (with_state)
			{
				slq.m_calls = m_calls;
			}
			return slq;
		}
		
		@Override
		public Object printState()
		{
			return m_calls;
		}
		
		@Override
		public SinkLastQueryable readState(/*@ non_null @*/ String reference, int in_arity, int out_arity, /*@ nullable @*/ Object o) throws ReadException
		{
			if (o == null || !(o instanceof Integer))
			{
				throw new ReadException("Unexpected state");
			}
			
			SinkLastQueryable slq = new SinkLastQueryable(reference, in_arity);
			slq.m_calls = (Integer) o;
			return slq;
		}
		
		@Override
		public List<TraceabilityNode> query(TraceabilityQuery q, Designator d, TraceabilityNode root, Tracer factory)
		{
			Designator head = d.peek();
			
			if (q instanceof UpstreamQuery)
			{
				if (head instanceof SinkContents)
				{
					return queryOutput(q, -1, d.tail(), root, factory);
				}
				if (head instanceof NthInput)
				{
					return super.query(q, d, root, factory);
				}
				return unknownLink(root, factory);
			}
			return super.query(q, head, root, factory);
		}
		
		@Override
		protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			Designator h_t_tail = tail.peek();
			Designator t_t_tail = tail.tail();
			if (!(h_t_tail instanceof NthElement))
			{
				// Unknown
				return unknownLink(root, factory);
			}
			NthElement nth = (NthElement) h_t_tail;
			int index = nth.getIndex();
			if (index < 0 || index >= getInputArity())
			{
				// Unknown element in the event front
				return unknownLink(root, factory);
			}
			ComposedDesignator cd = new ComposedDesignator(t_t_tail, new NthEvent(m_calls - 1), NthInput.get(index));
			TraceabilityNode node = factory.getObjectNode(cd, this);
			root.addChild(node, Quality.EXACT);
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
			leaves.add(node);
			return leaves;
		}
	}
	
	/**
	 * Designator that refers to the event front contained in the sink
	 */
	public static class SinkContents implements Designator
	{
		public static final transient SinkContents instance = new SinkContents();
		
		protected SinkContents()
		{
			super();
		}
		
		@Override
		public boolean appliesTo(Object o)
		{
			return o instanceof SinkLast;
		}

		@Override
		public Designator peek() 
		{
			return this;
		}

		@Override
		public Designator tail() 
		{
			return Designator.identity;
		}
		
		@Override
		public String toString()
		{
			return "Sink contents";
		}
	}
}
