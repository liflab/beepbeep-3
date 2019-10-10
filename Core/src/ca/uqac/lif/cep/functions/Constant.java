package ca.uqac.lif.cep.functions;

import java.util.ArrayList;
import java.util.List;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;

public class Constant extends SingleFunction
{
	protected Object m_value;
	
	public Constant(Object value)
	{
		super(0, 1);
		m_value = value;
	}

	@Override
	public Constant duplicate(boolean with_state) 
	{
		return new Constant(m_value);
	}
	
	@Override
	protected FunctionQueryable computeValue(Object[] inputs, Object[] outputs, Context c) 
	{
		outputs[0] = m_value;
		return new ConstantQueryable(toString());
	}

	static class ConstantQueryable extends FunctionQueryable
	{
		public ConstantQueryable(String reference)
		{
			super(reference, 0, 1);
		}
		
		@Override
		protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			TraceabilityNode node = factory.getObjectNode(HardValue.instance, this);
			root.addChild(node, Quality.EXACT);
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
			leaves.add(node);
			return leaves;
		}
	}

	@Override
	public Class<?> getInputType(int index) 
	{
		return null;
	}

	@Override
	public Class<?> getOutputType(int index) 
	{
		return m_value.getClass();
	}

	@Override
	public Object printState() 
	{
		return m_value;
	}

	@Override
	public Constant readState(int in_arity, int out_arity, Object o) 
	{
		return new Constant(o);
	}
	
	public static class HardValue implements Designator
	{
		public static final transient HardValue instance = new HardValue();
		
		private HardValue()
		{
			super();
		}
		
		@Override
		public boolean appliesTo(Object o)
		{
			return o instanceof Constant;
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
			return "Hard value";
		}
	}
}
