package ca.uqac.lif.cep.tmf;

import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;

public class CountDecimate extends SingleProcessor
{
	protected int m_interval;

	protected int m_currentCount;

	/*@ requires interval > 0 @*/
	public CountDecimate(int interval)
	{
		super(1, 1);
		m_interval = interval;
		m_currentCount = 0;
		m_queryable = new CountDecimateQueryable(toString(), 1, 1, interval);
	}

	@Override
	public void reset()
	{
		super.reset();
		m_currentCount = 0;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		if (m_currentCount == 0)
		{
			outputs.add(inputs);
		}
		m_currentCount = (m_currentCount + 1) % m_interval;
		return true;
	}

	@Override
	public CountDecimate duplicate(boolean with_state)
	{
		CountDecimate cd = new CountDecimate(m_interval);
		return (CountDecimate) copyInto(cd, with_state);
	}

	@Override
	public SingleProcessor copyInto(SingleProcessor p, boolean with_state)
	{
		p = super.copyInto(p, with_state);
		if (with_state)
		{
			((CountDecimate) p).m_currentCount = m_currentCount;
		}
		return p;
	}

	@Override
	protected SingleProcessor readState(Object state, int in_arity, int out_arity) throws ReadException 
	{
		if (!(state instanceof List))
		{
			throw new ReadException("Unexpected object");
		}
		List<?> list = (List<?>) state;
		if (list.size() != 2)
		{
			throw new ReadException("Unexpected list format");
		}
		try
		{
			CountDecimate cd = new CountDecimate((Integer) list.get(0));
			cd.m_currentCount = (Integer) list.get(1);
			return cd;
		}
		catch (ClassCastException e)
		{
			throw new ReadException(e);
		}
	}

	@Override
	protected Object printState()
	{
		List<Integer> list = new ArrayList<Integer>();
		list.add(m_interval);
		list.add(m_currentCount);
		return list;
	}
	
	@Override
	protected CountDecimateQueryable getQueryable(int in_arity, int out_arity)
	{
		return new CountDecimateQueryable(toString(), in_arity, out_arity, m_interval);
	}

	public static class CountDecimateQueryable extends ProcessorQueryable
	{
		protected int m_interval;

		public CountDecimateQueryable(String reference, int in_arity, int out_arity, int interval) 
		{
			super(reference, in_arity, out_arity);
			m_interval = interval;
		}

		@Override
		protected List<TraceabilityNode> queryInput(TraceabilityQuery q, int in_index, Designator tail, TraceabilityNode root, Tracer factory)
		{
			Designator t_head = tail.peek();
			Designator t_tail = tail.tail();
			if (!(t_head instanceof NthEvent))
			{
				// Unknown
				return super.queryOutput(q, in_index, t_tail, root, factory);
			}
			NthEvent nth = (NthEvent) t_head;
			int index = nth.getIndex();
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
			if (index % m_interval == 0)
			{
				ComposedDesignator cd = new ComposedDesignator(new NthEvent(index / m_interval), new NthOutput(in_index), t_tail);
				TraceabilityNode node = factory.getObjectNode(cd, this);
				root.addChild(node, Quality.EXACT);
				leaves.add(node);
			}
			else
			{
				// If index % interval != 0, the input event does not produce any output event
				TraceabilityNode node = factory.getObjectNode(Designator.nothing, this);
				root.addChild(node, Quality.EXACT);
				leaves.add(node);
			}
			return leaves;
		}

		@Override
		protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, Designator tail, TraceabilityNode root, Tracer factory)
		{
			Designator t_head = tail.peek();
			Designator t_tail = tail.tail();
			if (!(t_head instanceof NthEvent))
			{
				// Unknown
				return super.queryOutput(q, out_index, t_tail, root, factory);
			}
			NthEvent nth = (NthEvent) t_head;
			int index = nth.getIndex();
			ComposedDesignator cd = new ComposedDesignator(new NthEvent(index * m_interval), new NthInput(out_index), t_tail);
			TraceabilityNode node = factory.getObjectNode(cd, this);
			root.addChild(node, Quality.EXACT);
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
			leaves.add(node);
			return leaves;
		}
		
		@Override
		public Object printState()
		{
			return m_interval;
		}
		
		@Override
		public CountDecimateQueryable readState(/*@ non_null @*/ String reference, int in_arity, int out_arity, /*@ nullable @*/ Object state) throws ReadException
		{
			if (state == null || !(state instanceof Integer))
			{
				throw new ReadException("Interval must be a number");
			}
			return new CountDecimateQueryable(reference, in_arity, out_arity, (Integer) state);
		}
		
		@Override
		public CountDecimateQueryable duplicate(boolean with_state)
		{
			return new CountDecimateQueryable(m_reference, m_inputConnections.length, m_outputConnections.length, m_interval);
		}
	}
}
