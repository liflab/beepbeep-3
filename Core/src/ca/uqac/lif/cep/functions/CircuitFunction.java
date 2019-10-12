package ca.uqac.lif.cep.functions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Contextualizable;
import ca.uqac.lif.cep.StateDuplicable;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.DesignatedObject;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.ObjectNode;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.Trackable;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.circuit.CircuitElement;
import ca.uqac.lif.petitpoucet.circuit.CircuitQueryable;

public class CircuitFunction implements CircuitElement, Contextualizable, Function, Outputable, Trackable
{
	/*@ non_null @*/ protected CircuitConnection[] m_inputConnections;
	
	/*@ non_null @*/ protected CircuitConnection[] m_outputConnections;
	
	/*@ non_null @*/ protected Object[] m_outputValues;
	
	/*@ non_null @*/ protected Context m_context;
	
	/*@ non_null @*/ protected Function m_function;
	
	protected CircuitFunctionQueryable m_queryable;
	
	protected boolean m_computed;
	
	public static final transient String s_functionKey = "function";
	
	public static final transient String s_contentsKey = "contents";
	
	public static final transient String s_queryableKey = "queryable";
	
	public CircuitFunction(/*@ non_null @*/ Function f)
	{
		super();
		m_function = f;
		m_inputConnections = new CircuitConnection[f.getInputArity()];
		m_outputConnections = new CircuitConnection[f.getOutputArity()];
		m_outputValues = new Object[f.getOutputArity()];
		m_computed = false;
		m_context = new Context();
		m_queryable = new CircuitFunctionQueryable(f.toString(), f.getInputArity(), f.getOutputArity());
	}
	
	@Override
	public final Queryable getQueryable()
	{
		return m_queryable;
	}
	
	@Override
	public final int getInputArity()
	{
		return m_inputConnections.length;
	}
	
	@Override
	public final int getOutputArity()
	{
		return m_outputConnections.length;
	}
	
	@Override
	public void setToInput(int index, CircuitConnection conn)
	{
		try
		{
			m_inputConnections[index] = conn;
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	@Override
	public void setToOutput(int index, CircuitConnection conn)
	{
		try
		{
			m_outputConnections[index] = conn;
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	@Override
	public final CircuitConnection getInputConnection(int index)
	{
		try
		{
			return m_inputConnections[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	@Override
	public final CircuitConnection getOutputConnection(int index)
	{
		try
		{
			return m_outputConnections[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	public final Object getOutput()
	{
		return getOutput(0);
	}
	
	public final Object getOutput(int index)
	{
		if (!m_computed)
		{
			Object[] inputs = new Object[m_inputConnections.length];
			for (int i = 0; i < m_inputConnections.length; i++)
			{
				CircuitConnection cc = m_inputConnections[i];
				Outputable f = (Outputable) cc.getObject();
				inputs[i] = f.getOutput(cc.getIndex());
			}
			evaluate(inputs, m_outputValues, m_context); 
		}
		try
		{
			return m_outputValues[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	public void reset()
	{
		m_computed = false;
	}
	
	@Override
	public Object getContext(String key)
	{
		if (!m_context.containsKey(key))
		{
			return null;
		}
		return m_context.get(key);
	}

	@Override
	public void setContext(String key, Object value)
	{
		m_context.put(key, value);
	}
	
	@Override
	public final CircuitFunction duplicate()
	{
		return (CircuitFunction) duplicate(false);
	}
	
	@Override
	public CircuitFunction duplicate(boolean with_state)
	{
		CircuitFunction cf = new CircuitFunction(m_function.duplicate(with_state));
		return copyInto(cf, with_state);
	}
	
	protected CircuitFunction copyInto(/*@ non_null @*/ CircuitFunction cf, boolean with_state)
	{
		if (with_state)
		{
			cf.m_context.putAll(m_context);
			cf.m_queryable = m_queryable.duplicate(true);
			for (int i = 0; i < m_outputValues.length; i++)
			{
				cf.m_outputValues[i] = m_outputValues[i];
			}
		}
		return cf;
	}
	
	@Override
	public final Map<String,Object> print(ObjectPrinter<?> printer) throws PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(s_functionKey, m_function);
		map.put(s_queryableKey, m_queryable);
		Object contents = printState();
		if (contents != null)
		{
			map.put(s_contentsKey, contents);
		}
		return map;
	}
	
	protected Object printState()
	{
		return null;
	}
	
	protected CircuitFunction readState(Function f, Object o)
	{
		return new CircuitFunction(f);
	}

	@SuppressWarnings("unchecked")
	@Override
	public final Object read(ObjectReader<?> reader, Object o) throws ReadException 
	{
		Object r_o = reader.read(o);
		if (r_o == null || !(r_o instanceof Map))
		{
			throw new ReadException("Unexpected serialized object format");
		}
		try
		{
			Map<String,Object> map = (Map<String,Object>) r_o;
			if (!map.containsKey(s_functionKey) || !map.containsKey(s_queryableKey))
			{
				throw new ReadException("Unexpected map format");
			}
			Function f = (Function) map.get(s_functionKey);
			CircuitFunctionQueryable fq = (CircuitFunctionQueryable) map.get(s_queryableKey);
			Object contents = null;
			if (map.containsKey(s_contentsKey))
			{
				contents = map.get(s_contentsKey);
			}
			CircuitFunction cf = readState(f, contents);
			cf.m_queryable = fq;
			return cf;
		}
		catch (ClassCastException e)
		{
			throw new ReadException(e);
		}
	}
	
	@Override
	public final Queryable evaluate(Object[] inputs, Object[] outputs, Context c)
	{
		m_queryable.setQueryable(m_function.evaluate(inputs, outputs, c));
		m_computed = true;
		return m_queryable;
	}
	
	@Override
	public final Queryable evaluate(Object[] inputs, Object[] outputs) 
	{
		return evaluate(inputs, outputs, m_context);
	}

	@Override
	public Class<?> getInputType(int index)
	{
		return m_function.getInputType(index);
	}

	@Override
	public Class<?> getOutputType(int index) 
	{
		return m_function.getOutputType(index);
	}
	
	public static class CircuitFunctionQueryable extends CircuitQueryable implements StateDuplicable<CircuitFunctionQueryable>
	{
		/*@ nullable @*/ protected Queryable m_innerQueryable;
		
		public CircuitFunctionQueryable(String reference, int in_arity, int out_arity) 
		{
			super(reference, in_arity, out_arity);
		}
		
		/*@ nullable @*/ public Queryable getQueryable()
		{
			return m_innerQueryable;
		}
		
		public void setQueryable(/*@ nullable @*/ Queryable q)
		{
			m_innerQueryable = q;
		}
		
		@Override
		protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, 
				Designator tail, TraceabilityNode root, Tracer factory)
		{
			if (m_innerQueryable == null)
			{
				return unknownLink(root, factory);
			}
			ComposedDesignator cd = new ComposedDesignator(tail, new NthOutput(out_index));
			List<TraceabilityNode> leaves = m_innerQueryable.query(q, cd, root, factory);
			List<TraceabilityNode> new_leaves = new ArrayList<TraceabilityNode>(leaves.size());
			for (TraceabilityNode leaf : leaves)
			{
				if (!(leaf instanceof ObjectNode))
				{
					new_leaves.add(leaf);
					continue;
				}
				ObjectNode on_leaf = (ObjectNode) leaf;
				DesignatedObject leaf_dob = on_leaf.getDesignatedObject();
				if (leaf_dob.getDesignator().peek() instanceof NthInput)
				{
					// Change designated object from inner function
					// to the encasing CircuitFunction
					TraceabilityNode new_leaf = factory.getObjectNode(leaf_dob.getDesignator(), this);
					on_leaf.addChild(new_leaf, Quality.EXACT);
					new_leaves.add(new_leaf);
				}
				else
				{
					// Not an "n-th input": dunno
					TraceabilityNode unknown = factory.getUnknownNode();
					on_leaf.addChild(unknown, Quality.NONE);
					new_leaves.add(unknown);
				}
			}
			return new_leaves;
		}

		@Override
		protected List<TraceabilityNode> queryInput(TraceabilityQuery q, int in_index, Designator tail, TraceabilityNode root, Tracer factory)
		{
			return unknownLink(root, factory);
		}

		@Override
		public CircuitFunctionQueryable duplicate()
		{
			return duplicate(false);
		}

		@SuppressWarnings("unchecked")
		@Override
		/*@ non_null @*/ public CircuitFunctionQueryable duplicate(boolean with_state) 
		{
			CircuitFunctionQueryable cf = new CircuitFunctionQueryable(m_reference, getInputArity(), getOutputArity());
			if (with_state && cf.m_innerQueryable != null)
			{
				cf.m_innerQueryable = ((StateDuplicable<Queryable>) m_innerQueryable).duplicate(with_state);
			}
			return cf;
		}
		
	}
}
