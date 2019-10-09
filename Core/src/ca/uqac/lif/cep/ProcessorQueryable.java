package ca.uqac.lif.cep;

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
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.DownstreamQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.UpstreamQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.circuit.CircuitQueryable;

public class ProcessorQueryable implements CircuitQueryable, Readable, Printable, StateDuplicable<Queryable>
{
	/*@ non_null @*/ protected QueryableCircuitConnection[] m_inputConnections;

	/*@ non_null @*/ protected QueryableCircuitConnection[] m_outputConnections;
	
	/*@ non_null @*/ protected String m_reference;
	
	public static final transient String s_arityKey = "arity";
	
	public static final transient String s_contentsKey = "contents";
	
	public static final transient String s_referenceKey = "ref";
	
	public ProcessorQueryable(/*@ non_null @*/ String reference, int in_arity, int out_arity)
	{
		super();
		m_reference = reference;
		m_inputConnections = new QueryableCircuitConnection[in_arity];
		m_outputConnections = new QueryableCircuitConnection[out_arity];
	}

	@Override
	public List<TraceabilityNode> query(TraceabilityQuery q, Designator d, TraceabilityNode root, Tracer factory)
	{
		List<TraceabilityNode> out_list = new ArrayList<TraceabilityNode>();
		Designator head = d.peek();
		Designator tail = d.tail();
		if (q instanceof UpstreamQuery && head instanceof NthInput)
		{
			int index = ((NthInput) head).getIndex();
			if (index < 0 || index >= m_inputConnections.length)
			{
				TraceabilityNode node = factory.getUnknownNode();
				root.addChild(node, Quality.NONE);
				out_list.add(node);
				return out_list;
			}
			CircuitConnection cc = m_inputConnections[index];
			if (cc != null)
			{
				ComposedDesignator cd = new ComposedDesignator(tail, new NthOutput(cc.getIndex()));
				TraceabilityNode node = factory.getObjectNode(cd, cc.getObject());
				root.addChild(node, Quality.EXACT);
				out_list.add(node);
			}
			return out_list;
		}
		if (q instanceof DownstreamQuery && head instanceof NthOutput)
		{
			int index = ((NthOutput) head).getIndex();
			if (index < 0 || index >= m_outputConnections.length)
			{
				TraceabilityNode node = factory.getUnknownNode();
				root.addChild(node, Quality.NONE);
				out_list.add(node);
				return out_list;
			}
			CircuitConnection cc = m_outputConnections[index];
			if (cc != null)
			{
				ComposedDesignator cd = new ComposedDesignator(tail, new NthInput(cc.getIndex()));
				TraceabilityNode node = factory.getObjectNode(cd, cc.getObject());
				root.addChild(node, Quality.EXACT);
				out_list.add(node);
			}
			return out_list;
		}
		if (head instanceof NthOutput && ((NthOutput) head).getIndex() >= 0 && ((NthOutput) head).getIndex() < m_outputConnections.length)
		{
			return queryOutput(q, ((NthOutput) head).getIndex(), tail, root, factory);
		}
		if (head instanceof NthInput && ((NthInput) head).getIndex() >= 0 && ((NthInput) head).getIndex() < m_inputConnections.length)
		{
			return queryInput(q, ((NthInput) head).getIndex(), tail, root, factory);
		}
		TraceabilityNode node = factory.getUnknownNode();
		root.addChild(node, Quality.NONE);
		out_list.add(node);
		return out_list;
	}
	
	public String getReference()
	{
		return m_reference;
	}

	@Override
	public void setToInput(int index, CircuitConnection connection) 
	{
		m_inputConnections[index] = (QueryableCircuitConnection) connection;
	}

	@Override
	public void setToOutput(int index, CircuitConnection connection) 
	{
		m_outputConnections[index] = (QueryableCircuitConnection) connection;
	}

	@Override
	public int getInputArity() 
	{
		return m_inputConnections.length;
	}

	@Override
	public int getOutputArity()
	{
		return m_outputConnections.length;
	}

	@Override
	public QueryableCircuitConnection getInputConnection(int index) 
	{
		return m_inputConnections[index];
	}

	@Override
	public QueryableCircuitConnection getOutputConnection(int index) 
	{
		return m_outputConnections[index];
	}

	@Override
	public final ProcessorQueryable duplicate() 
	{
		return duplicate(false);
	}
	
	@Override
	public String toString()
	{
		return m_reference;
	}

	public static class QueryableCircuitConnection implements CircuitConnection
	{
		protected int m_index;

		protected CircuitQueryable m_queryable;

		public QueryableCircuitConnection(int index, CircuitQueryable q)
		{
			super();
			m_index = index;
			m_queryable = q;
		}

		@Override
		public int getIndex() 
		{
			return m_index;
		}

		@Override
		public CircuitQueryable getObject()
		{
			return m_queryable;
		}
	}

	protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, 
			Designator tail, TraceabilityNode root, Tracer factory)
	{
		return unknownLink(root, factory);
	}

	protected List<TraceabilityNode> queryInput(TraceabilityQuery q, int in_index, Designator tail, TraceabilityNode root, Tracer factory)
	{
		return unknownLink(root, factory);
	}
	
	protected List<TraceabilityNode> unknownLink(TraceabilityNode root, Tracer factory)
	{
		TraceabilityNode node = factory.getUnknownNode();
		root.addChild(node, Quality.NONE);
		List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
		leaves.add(node);
		return leaves;
	}

	@Override
	public ProcessorQueryable duplicate(boolean with_state) 
	{
		return new ProcessorQueryable(m_reference, m_inputConnections.length, m_outputConnections.length);
	}

	@Override
	public final Object print(ObjectPrinter<?> printer) throws PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		List<Integer> list = new ArrayList<Integer>(2);
		list.add(m_inputConnections.length);
		list.add(m_outputConnections.length);
		map.put(s_arityKey, list);
		map.put(s_referenceKey, m_reference);
		Object o = printState();
		if (o != null)
		{
			map.put(s_contentsKey, o);
		}
		return printer.print(map);
	}

	@SuppressWarnings("unchecked")
	@Override
	public final Object read(ObjectReader<?> reader, Object o) throws ReadException
	{
		Object r_o = reader.read(o);
		if (!(r_o instanceof Map))
		{
			throw new ReadException("Unexpected format for queryable");
		}
		Map<?,?> map = (Map<?,?>) r_o;
		try
		{
			List<Integer> list = (List<Integer>) getOrDefault(map, s_arityKey, null);
			if (list == null)
			{
				throw new ReadException("Unexpected format for list");
			}
			Object state = getOrDefault(map, s_contentsKey, null);
			String reference = (String) getOrDefault(map, s_referenceKey, null);
			if (reference == null)
			{
				throw new ReadException("Reference string is null");
			}
			int in_arity = list.get(0);
			int out_arity = list.get(1);
			return readState(reference, in_arity, out_arity, state);
		}
		catch (ClassCastException e)
		{
			throw new ReadException(e);
		}
		catch (IndexOutOfBoundsException e)
		{
			throw new ReadException(e);
		}
	}
	
	public Object printState()
	{
		return null;
	}
	
	public ProcessorQueryable readState(/*@ non_null @*/ String reference, int in_arity, int out_arity, /*@ nullable @*/ Object state) throws ReadException
	{
		return new ProcessorQueryable(reference, in_arity, out_arity);
	}
	
	protected static Object getOrDefault(Map<?,?> map, Object key, Object default_value)
	{
		if (!map.containsKey(key)) 
		{
			return default_value;
		}
		return map.get(key);
	}
}
