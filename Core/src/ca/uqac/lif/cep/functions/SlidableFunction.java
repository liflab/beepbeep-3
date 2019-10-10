package ca.uqac.lif.cep.functions;

import java.util.ArrayList;
import java.util.List;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.CausalityQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.ConsequenceQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.ProvenanceQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.TaintQuery;
import ca.uqac.lif.petitpoucet.common.NthOf;

public interface SlidableFunction extends Function
{
	@Override
	public SlidableFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context context);
	
	@Override
	public SlidableFunctionQueryable evaluate(Object[] inputs, Object[] outputs);
	
	public SlidableFunctionQueryable devaluate(Object[] inputs, Object[] outputs, Context context);
	
	public SlidableFunctionQueryable devaluate(Object[] inputs, Object[] outputs);
	
	public static class SlidableFunctionQueryable extends FunctionQueryable
	{
		protected int m_numEvaluate;
		
		protected int m_numDevaluate;
		
		public SlidableFunctionQueryable(String reference)
		{
			super(reference, 1, 1);
			m_numEvaluate = 0;
			m_numDevaluate = 0;
		}
		
		public void addCallToEvaluate()
		{
			m_numEvaluate++;
		}
		
		public void addCallToDevaluate()
		{
			m_numDevaluate++;
		}
		
		public void reset()
		{
			m_numEvaluate = 0;
			m_numDevaluate = 0;
		}
		
		@Override
		protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			Designator t_head = tail.peek();
			Designator t_tail = tail.tail();
			if (!(t_head instanceof PastOutput))
			{
				return unknownLink(root, factory);
			}
			int num_past_output = ((PastOutput) t_head).getIndex();
			if (q instanceof ProvenanceQuery)
			{
				return pastInputsLink(num_past_output, t_tail, root, factory);
			}
			if (q instanceof CausalityQuery)
			{
				return queryCausality(num_past_output, t_tail, root, factory);
			}
			return unknownLink(root, factory);
		}
		
		@Override
		protected List<TraceabilityNode> queryInput(TraceabilityQuery q, int in_index, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			Designator t_head = tail.peek();
			Designator t_tail = tail.tail();
			if (!(t_head instanceof PastInput))
			{
				return unknownLink(root, factory);
			}
			int num_past_input = ((PastInput) t_head).getIndex();
			if (q instanceof TaintQuery)
			{
				return pastOutputsLink(num_past_input, t_tail, root, factory);
			}
			if (q instanceof ConsequenceQuery)
			{
				return queryConsequence(num_past_input, t_tail, root, factory);
			}
			return unknownLink(root, factory);
		}
	
		protected List<TraceabilityNode> pastInputsLink(int out_index, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>();
			for (int i = m_numDevaluate; i < m_numEvaluate; i++)
			{
				TraceabilityNode and = factory.getAndNode();
				root.addChild(and, Quality.EXACT);
				ComposedDesignator cd = new ComposedDesignator(tail, new PastInput(i));
				TraceabilityNode node = factory.getObjectNode(cd, this);
				and.addChild(node, Quality.EXACT);
				leaves.add(node);
			}
			return leaves;
		}
		
		@Override
		protected List<TraceabilityNode> queryCausality(int out_index, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			return pastInputsLink(out_index, tail, root, factory);
		}
		
		protected List<TraceabilityNode> pastOutputsLink(int num_past_input, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>();
			int width = m_numEvaluate - m_numDevaluate;
			int start = Math.max(m_numDevaluate, num_past_input);
			int end = Math.min(num_past_input + width, m_numEvaluate);
			for (int i = start; i < end; i++)
			{
				TraceabilityNode and = factory.getAndNode();
				root.addChild(and, Quality.EXACT);
				ComposedDesignator cd = new ComposedDesignator(tail, new PastOutput(i));
				TraceabilityNode node = factory.getObjectNode(cd, this);
				and.addChild(node, Quality.EXACT);
				leaves.add(node);
			}
			return leaves;
		}
		
		@Override
		protected List<TraceabilityNode> queryConsequence(int num_past_input, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			return pastOutputsLink(num_past_input, tail, root, factory);
		}
		
		@Override
		protected List<Integer> printState()
		{
			List<Integer> list = new ArrayList<Integer>(2);
			list.add(m_numEvaluate);
			list.add(m_numDevaluate);
			return list;
		}
		
		@Override
		protected SlidableFunctionQueryable readState(String reference, int in_arity, int out_arity, Object o) throws ReadException
		{
			if (o == null || !(o instanceof List))
			{
				throw new ReadException("Unexpected list format");
			}
			List<?> list = (List<?>) o;
			if (list.size() != 2 || !(list.get(0) instanceof Integer) || !(list.get(1) instanceof Integer))
			{
				throw new ReadException("Unexpected list format");
			}
			SlidableFunctionQueryable sfq = new SlidableFunctionQueryable(reference);
			sfq.m_numEvaluate = (Integer) list.get(0);
			sfq.m_numDevaluate = (Integer) list.get(1);
			return sfq;
		}
	}
	
	public static class PastInput extends NthOf
	{
		public PastInput(int index)
		{
			super(index);
		}

		@Override
		public boolean appliesTo(Object o)
		{
			return o instanceof SlidableFunction;
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
			return "Past input #" + m_index;
		}
	}
	
	public static class PastOutput extends NthOf
	{
		public PastOutput(int index)
		{
			super(index);
		}

		@Override
		public boolean appliesTo(Object o)
		{
			return o instanceof SlidableFunction;
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
			return "Past output #" + m_index;
		}
	}
}
