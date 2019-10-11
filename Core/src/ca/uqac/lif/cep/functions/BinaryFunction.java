package ca.uqac.lif.cep.functions;

import java.util.ArrayList;
import java.util.List;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;

public abstract class BinaryFunction<T,U,V> implements Function
{
	/*@ non_null @*/ protected Class<? extends T> m_inputTypeLeft;
	
	/*@ non_null @*/ protected Class<? extends U> m_inputTypeRight;
	
	/*@ non_null @*/ protected Class<? extends V> m_outputType;
	
	public BinaryFunction(Class<? extends T> t_left, Class<? extends U> t_right, Class<? extends V> t_output)
	{
		super();
		m_inputTypeLeft = t_left;
		m_inputTypeRight = t_right;
		m_outputType = t_output;
	}
	
	@Override
	public final int getInputArity()
	{
		return 2;
	}
	
	@Override
	public final int getOutputArity()
	{
		return 1;
	}
	
	@Override
	public Class<? extends V> getOutputType(int index)
	{
		return m_outputType;
	}
	
	@Override
	public Class<?> getInputType(int index)
	{
		if (index == 0)
		{
			return m_inputTypeLeft;
		}
		if (index == 1)
		{
			return m_inputTypeRight;
		}
		return null;
	}
	
	@Override
	public final BinaryFunctionQueryable evaluate(Object[] inputs, Object[] outputs) 
	{
		return evaluate(inputs, outputs, null);
	}
	
	@Override
	public void reset()
	{
		// Nothing to do
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public BinaryFunction<T,U,V> duplicate() 
	{
		return (BinaryFunction<T,U,V>) duplicate(false);
	}
	
	public static class BinaryFunctionQueryable extends FunctionQueryable
	{
		public enum Inputs {LEFT, RIGHT, BOTH, ANY}
		
		/*@ non_null @*/ protected Inputs m_inputs;
		
		public BinaryFunctionQueryable(/*@ non_null @*/ String reference, /*@ non_null @*/ Inputs i)
		{
			super(reference, 2, 1);
			m_inputs = i;
		}
		
		@Override
		protected List<TraceabilityNode> queryCausality(int out_index, 
				Designator d, TraceabilityNode root, Tracer factory)
		{
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>();
			switch (m_inputs)
			{
			case LEFT:
			{
				ComposedDesignator cd = new ComposedDesignator(d, new NthInput(0));
				TraceabilityNode node = factory.getObjectNode(cd, this);
				root.addChild(node, Quality.EXACT);
				leaves.add(node);
				return leaves;
			}
			case RIGHT:
			{
				ComposedDesignator cd = new ComposedDesignator(d, new NthInput(1));
				TraceabilityNode node = factory.getObjectNode(cd, this);
				root.addChild(node, Quality.EXACT);
				leaves.add(node);
				return leaves;
			}
			case ANY:
			{
				TraceabilityNode or = factory.getOrNode();
				root.addChild(or, Quality.EXACT);
				ComposedDesignator cd1 = new ComposedDesignator(d, new NthInput(0));
				TraceabilityNode node1 = factory.getObjectNode(cd1, this);
				or.addChild(node1, Quality.EXACT);
				leaves.add(node1);
				ComposedDesignator cd2 = new ComposedDesignator(d, new NthInput(1));
				TraceabilityNode node2 = factory.getObjectNode(cd2, this);
				or.addChild(node2, Quality.EXACT);
				leaves.add(node2);
				return leaves;
			}
			default:
				return allInputsLink(out_index, d, root, factory);
			}
		}
		
		@Override
		protected List<TraceabilityNode> queryConsequence(int in_index, 
				Designator d, TraceabilityNode root, Tracer factory)
		{
			List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>();
			switch (m_inputs)
			{
			case LEFT:
			{
				Designator cd = new ComposedDesignator(d, new NthOutput(0));
				if (in_index != 0)
				{
					cd = Designator.nothing;
				}
				TraceabilityNode node = factory.getObjectNode(cd, this);
				root.addChild(node, Quality.EXACT);
				leaves.add(node);
				return leaves;
			}
			case RIGHT:
			{
				Designator cd = new ComposedDesignator(d, new NthOutput(0));
				if (in_index != 1)
				{
					cd = Designator.nothing;
				}
				TraceabilityNode node = factory.getObjectNode(cd, this);
				root.addChild(node, Quality.EXACT);
				leaves.add(node);
				return leaves;
			}
			default:
				return allOutputsLink(in_index, d, root, factory);
			}
		}
		
		@Override
		protected Integer printState()
		{
			switch (m_inputs)
			{
			case LEFT:
				return 1;
			case RIGHT:
				return 2;
			case ANY:
				return 3;
			default:
				return 0;
			}
		}
		
		@Override
		protected BinaryFunctionQueryable readState(String reference, int in_arity, int out_arity, Object o) throws ReadException
		{
			if (o == null || !(o instanceof Integer))
			{
				throw new ReadException("Unexpected number format");
			}
			int index = (Integer) o;
			if (index == 1)
			{
				return new BinaryFunctionQueryable(reference, Inputs.LEFT);
			}
			if (index == 2)
			{
				return new BinaryFunctionQueryable(reference, Inputs.RIGHT);
			}
			if (index == 3)
			{
				return new BinaryFunctionQueryable(reference, Inputs.ANY);
			}
			return new BinaryFunctionQueryable(reference, Inputs.BOTH);
		}
		
		@Override
		public BinaryFunctionQueryable duplicate(boolean with_state)
		{
			return new BinaryFunctionQueryable(m_reference, m_inputs);
		}
	}
	
	@Override
	public abstract BinaryFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c);
}
