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
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;

public class Passthrough extends SingleProcessor
{
	public Passthrough(int arity)
	{
		super(arity, arity);
		m_queryable = new PassthroughQueryable(toString(), arity, arity);
	}
	
	public Passthrough()
	{
		this(1);
	}

	@Override
	public Passthrough duplicate(boolean with_state)
	{
		Passthrough pt = new Passthrough(getInputArity());
		return (Passthrough) copyInto(pt, with_state);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
	{
		outputs.add(inputs);
		return true;
	}

	@Override
	protected SingleProcessor readState(Object state, int in_arity, int out_arity) throws ReadException
	{
		return new Passthrough(in_arity);
	}

	@Override
	protected Object printState() 
	{
		return null;
	}
	
	@Override
	protected PassthroughQueryable getQueryable(int in_arity, int out_arity)
	{
		return new PassthroughQueryable(toString(), in_arity, out_arity);
	}
	
	public static class PassthroughQueryable extends ProcessorQueryable
	{
		public PassthroughQueryable(String reference, int in_arity, int out_arity) 
		{
			super(reference, in_arity, out_arity);
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
			ComposedDesignator cd = new ComposedDesignator(t_tail, new NthEvent(index), new NthOutput(in_index));
			TraceabilityNode node = factory.getObjectNode(cd, this);
			root.addChild(node, Quality.EXACT);
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
			leaves.add(node);
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
			ComposedDesignator cd = new ComposedDesignator(t_tail, new NthEvent(index), new NthInput(out_index));
			TraceabilityNode node = factory.getObjectNode(cd, this);
			root.addChild(node, Quality.EXACT);
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
			leaves.add(node);
			return leaves;
		}
		
		@Override
		public Object printState()
		{
			return null;
		}
		
		@Override
		public PassthroughQueryable readState(/*@ non_null @*/ String reference, int in_arity, int out_arity, /*@ nullable @*/ Object state) throws ReadException
		{
			return new PassthroughQueryable(reference, in_arity, out_arity);
		}
		
		@Override
		public PassthroughQueryable duplicate(boolean with_state)
		{
			return new PassthroughQueryable(m_reference, m_inputConnections.length, m_outputConnections.length);
		}
	}
}
