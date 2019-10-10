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
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.circuit.CircuitQueryable;

public class ProcessorQueryable extends CircuitQueryable implements Readable, Printable, StateDuplicable<Queryable>
{		
	public static final transient String s_arityKey = "arity";
	
	public static final transient String s_contentsKey = "contents";
	
	public static final transient String s_referenceKey = "ref";
	
	public ProcessorQueryable(/*@ non_null @*/ String reference, int in_arity, int out_arity)
	{
		super(reference, in_arity, out_arity);
	}

	@Override
	public final ProcessorQueryable duplicate() 
	{
		return duplicate(false);
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
}
