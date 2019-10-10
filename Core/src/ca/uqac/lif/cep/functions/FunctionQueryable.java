package ca.uqac.lif.cep.functions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.cep.StateDuplicable;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.CausalityQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.ConsequenceQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.ProvenanceQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.TaintQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.circuit.CircuitQueryable;

public class FunctionQueryable extends CircuitQueryable implements StateDuplicable<FunctionQueryable>, Printable, Readable
{
	public static final transient String s_arityKey = "arity";

	public static final transient String s_contentsKey = "contents";

	public static final transient String s_referenceKey = "reference";

	public FunctionQueryable(/*@ non_null @*/ String reference, int in_arity, int out_arity)
	{
		super(reference, in_arity, out_arity);
	}

	@Override
	protected List<TraceabilityNode> queryInput(TraceabilityQuery q, int in_index, 
			Designator tail, TraceabilityNode root, Tracer factory)
	{
		if (q instanceof TaintQuery)
		{
			allInputsLink(in_index, tail, root, factory);
		}
		if (q instanceof ConsequenceQuery)
		{
			return queryConsequence(in_index, tail, root, factory);
		}
		return unknownLink(root, factory);
	}

	@Override
	protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, 
			Designator tail, TraceabilityNode root, Tracer factory)
	{
		if (q instanceof ProvenanceQuery)
		{
			return allInputsLink(out_index, tail, root, factory);
		}
		if (q instanceof CausalityQuery)
		{
			return queryCausality(out_index, tail, root, factory);
		}
		return unknownLink(root, factory);
	}

	protected List<TraceabilityNode> queryCausality(int out_index, 
			Designator d, TraceabilityNode root, Tracer factory)
	{
		return allInputsLink(out_index, d, root, factory);
	}

	protected List<TraceabilityNode> queryConsequence(int in_index, 
			Designator d, TraceabilityNode root, Tracer factory)
	{
		return allOutputsLink(in_index, d, root, factory);
	}

	protected List<TraceabilityNode> allInputsLink(int out_index, 
			Designator t_tail, TraceabilityNode root, Tracer factory)
	{
		List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>();
		TraceabilityNode and = factory.getAndNode();
		root.addChild(and, Quality.EXACT);
		for (int i = 0; i < m_inputConnections.length; i++)
		{
			ComposedDesignator cd = new ComposedDesignator(t_tail, new NthInput(i));
			TraceabilityNode node = factory.getObjectNode(cd, this);
			and.addChild(node, Quality.EXACT);
			leaves.add(node);
		}
		return leaves;
	}

	protected List<TraceabilityNode> allOutputsLink(int out_index, 
			Designator t_tail, TraceabilityNode root, Tracer factory)
	{
		List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>();
		TraceabilityNode and = factory.getAndNode();
		root.addChild(and, Quality.EXACT);
		for (int i = 0; i < m_outputConnections.length; i++)
		{
			ComposedDesignator cd = new ComposedDesignator(t_tail, new NthOutput(i));
			TraceabilityNode node = factory.getObjectNode(cd, this);
			and.addChild(node, Quality.EXACT);
			leaves.add(node);
		}
		return leaves;
	}

	@Override
	public final FunctionQueryable duplicate() 
	{
		return duplicate(false);
	}

	@SuppressWarnings("unchecked")
	@Override
	public FunctionQueryable read(ObjectReader<?> reader, Object o) throws ReadException 
	{
		Object r_o = reader.read(o);
		if (r_o == null || !(r_o instanceof Map))
		{
			throw new ReadException("Unexpected serialized object format");
		}
		try
		{
			Map<String,Object> map = (Map<String,Object>) r_o;
			if (!map.containsKey(s_arityKey) || !map.containsKey(s_referenceKey))
			{
				throw new ReadException("Unexpected map format");
			}
			List<Integer> arities = (List<Integer>) map.get(s_arityKey);
			if (arities.size() != 2)
			{
				throw new ReadException("Unexpected object format for arities");
			}
			Object contents = null;
			if (map.containsKey(s_contentsKey))
			{
				contents = map.get(s_contentsKey);
			}
			return readState((String) map.get(s_referenceKey), arities.get(0), arities.get(1), contents);
		}
		catch (ClassCastException e)
		{
			throw new ReadException(e);
		}
	}

	@Override
	public final Object print(ObjectPrinter<?> printer) throws PrintException 
	{
		Map<String,Object> map = new HashMap<String,Object>();
		List<Integer> arities = new ArrayList<Integer>(2);
		map.put(s_arityKey, arities);
		map.put(s_referenceKey, m_reference);
		Object contents = printState();
		if (contents != null)
		{
			map.put(s_contentsKey, contents);
		}
		return map;
	}

	@Override
	public FunctionQueryable duplicate(boolean with_state) 
	{
		return new FunctionQueryable(m_reference, m_inputConnections.length, m_outputConnections.length);
	}

	protected Object printState() throws PrintException
	{
		// Nothing to do
		return null;
	}

	protected FunctionQueryable readState(String reference, int in_arity, int out_arity, Object o) throws ReadException
	{
		return new FunctionQueryable(reference, in_arity, out_arity);
	}

}
