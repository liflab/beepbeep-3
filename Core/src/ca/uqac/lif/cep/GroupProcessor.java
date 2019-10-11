package ca.uqac.lif.cep;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.cep.functions.CircuitFunction;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.Trackable;
import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;
import ca.uqac.lif.petitpoucet.circuit.CircuitElement;

public class GroupProcessor implements Processor, Printable, Readable
{
	/*@ non_null @*/ protected Context m_context;

	/*@ non_null @*/ protected Set<Processor> m_innerProcessors;

	/*@ non_null @*/ protected InputProxyConnection[] m_inputPlaceholders;

	/*@ non_null @*/ protected OutputProxyConnection[] m_outputPlaceholders;
	
	static final transient String s_processorsKey = "processors";
	
	static final transient String s_connectionsKey = "connections";
	
	static final transient String s_arityKey = "arity";
	
	static final transient String s_contextKey = "context";

	public GroupProcessor(int in_arity, int out_arity)
	{
		super();
		m_context = new Context();
		m_innerProcessors = new HashSet<Processor>();
		m_inputPlaceholders = new InputProxyConnection[in_arity];
		for (int i = 0; i < in_arity; i++)
		{
			m_inputPlaceholders[i] = new InputProxyConnection(i);
		}
		m_outputPlaceholders = new OutputProxyConnection[out_arity];
		for (int i = 0; i < out_arity; i++)
		{
			m_outputPlaceholders[i] = new OutputProxyConnection(i);
		}
	}

	/**
	 * @deprecated This method has no effect as of version 0.11. As for any
	 * other processor chain, a {@link GroupProcessor} that contains sources
	 * cannot be used in push mode.
	 * @param b Whether to notify the sources 
	 * @return This group
	 */
	@Deprecated
	public final GroupProcessor notifySources(boolean b)
	{
		throw new UnsupportedOperationException("Method GroupProcessor.notifySources is no longer supported");
	}

	public void add(Processor ... processors)
	{
		for (Processor p : processors)
		{
			m_innerProcessors.add(p);
		}
	}

	public void add(Collection<Processor> processors)
	{
		m_innerProcessors.addAll(processors);
	}

	/**
	 * @deprecated Use {@link #add(Processor...)}
	 * @param processors
	 */
	public final void addProcessors(Processor ... processors)
	{
		add(processors);
	}

	@Override
	public void setToInput(int index, CircuitConnection connection)
	{
		setPullableInput(index, (Pullable) connection);
	}

	@Override
	public void setToOutput(int index, CircuitConnection connection) 
	{
		setPushableOutput(index, (Pushable) connection);
	}

	@Override
	public int getInputArity() 
	{
		return m_inputPlaceholders.length;
	}

	@Override
	public int getOutputArity() 
	{
		return m_outputPlaceholders.length;
	}

	@Override
	public Object getContext(String key) 
	{
		return m_context.get(key);
	}

	@Override
	public void setContext(String key, Object value)
	{
		m_context.put(key, value);
	}

	public void associateInput(int i, Processor p, int j)
	{
		m_inputPlaceholders[i].setPushable(p.getPushableInput(j));
		p.setPullableInput(j, m_inputPlaceholders[i]);
	}

	public void associateOutput(int i, Processor p, int j)
	{
		m_outputPlaceholders[i].setPullable(p.getPullableOutput(j));
		p.setPushableOutput(j, m_outputPlaceholders[i]);
	}

	@Override
	public void start()
	{
		for (Processor p : m_innerProcessors)
		{
			p.start();
		}
	}

	@Override
	public void stop()
	{
		for (Processor p : m_innerProcessors)
		{
			p.stop();
		}
	}

	@Override
	public GroupProcessor duplicate(boolean with_state) 
	{
		GroupProcessor gp = new GroupProcessor(m_inputPlaceholders.length, m_outputPlaceholders.length);
		return copyInto(gp, with_state, new HashMap<Processor,Processor>());
	}

	protected GroupProcessor copyInto(GroupProcessor gp, boolean with_state, Map<Processor,Processor> correspondences)
	{
		if (with_state)
		{
			gp.m_context.putAll(m_context);
		}
		for (Processor p : m_innerProcessors)
		{
			Processor p_dup = p.duplicate(with_state);
			correspondences.put(p, p_dup);
			gp.add(p_dup);
		}
		for (Map.Entry<Processor,Processor> e : correspondences.entrySet())
		{
			Processor p_src = e.getKey();
			Processor p_dst = e.getValue();
			for (int i = 0; i < p_src.getInputArity(); i++)
			{
				CircuitConnection cc = p_src.getInputConnection(i);
				if (cc == null)
				{
					throw new ProcessorException("Processor " + p_src + " has no connection on input pipe " + i);
				}
				Processor src_upstream = (Processor) cc.getObject();
				if (src_upstream == this)
				{
					// This happens when processor is connected to the group's ProxyConnection
					continue;
				}
				Processor dst_upstream = correspondences.get(src_upstream);;
				assert dst_upstream != null;
				Connector.connect(dst_upstream, cc.getIndex(), p_dst, i);
			}
		}
		for (int i = 0; i < m_inputPlaceholders.length; i++)
		{
			ProxyConnection pc = m_inputPlaceholders[i];
			Pushable push = pc.getPushable();
			if (push != null)
			{
				Processor target_p = (Processor) push.getObject();
				gp.associateInput(i, correspondences.get(target_p), pc.getIndex());
			}
		}
		for (int i = 0; i < m_outputPlaceholders.length; i++)
		{
			ProxyConnection pc = m_outputPlaceholders[i];
			Pullable pull = pc.getPullable();
			if (pull != null)
			{
				Processor source_p = (Processor) pull.getObject();
				gp.associateOutput(i, correspondences.get(source_p), pc.getIndex());
			}
		}
		return gp;
	}

	@Override
	public final GroupProcessor duplicate() 
	{
		return duplicate(false);
	}

	@Override
	public Pushable getPushableInput(int index) 
	{
		try
		{
			return m_inputPlaceholders[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public final Pushable getPushableInput()
	{
		return getPushableInput(0);
	}

	@Override
	public Pullable getPullableOutput(int index) 
	{
		try
		{
			return m_outputPlaceholders[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public final Pullable getPullableOutput() 
	{
		return getPullableOutput(0);
	}

	@Override
	public void setPullableInput(int index, Pullable p) 
	{
		try
		{
			m_inputPlaceholders[index].setPullable(p);
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public void setPushableOutput(int index, Pushable p) 
	{
		try
		{
			m_outputPlaceholders[index].setPushable(p);
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public void reset() 
	{
		for (Processor p : m_innerProcessors)
		{
			p.reset();
		}
	}

	protected abstract class ProxyConnection implements Pullable, Pushable
	{
		protected final int m_index;

		/*@ null @*/ protected Pushable m_pushable;

		/*@ null @*/ protected Pullable m_pullable;

		public ProxyConnection(int index)
		{
			super();
			m_index = index;
		}

		@Override
		/*@ pure @*/ public int getIndex()
		{
			return m_index;
		}

		public void setPullable(/*@ non_null @*/ Pullable p)
		{
			m_pullable = p;
		}

		/*@ pure null @*/ public Pullable getPullable()
		{
			return m_pullable;
		}

		public void setPushable(/*@ non_null @*/ Pushable p)
		{
			m_pushable = p;
		}

		/*@ pure null @*/ public Pushable getPushable()
		{
			return m_pushable;
		}

		@Override
		/*@ pure non_null @*/ public Processor getObject() 
		{
			return GroupProcessor.this;
		}

		@Override
		public void push(Object o) 
		{
			m_pushable.push(o);
		}

		@Override
		public Object pull()
		{
			return m_pullable.pull();
		}

		@Override
		/*@ pure @*/ public boolean hasNext() 
		{
			return m_pullable.hasNext();
		}

		@Override
		public Object next() 
		{
			return pull();
		}

		@Override
		public void end() 
		{
			m_pushable.end();
		}
		
		@Override
		public NextStatus hasNextSoft()
		{
			if (hasNext())
			{
				return NextStatus.YES;
			}
			return NextStatus.NO;
		}

		@Override
		public Object pullSoft() 
		{
			return pull();
		}
		
		@Override
		public void remove()
		{
			throw new UnsupportedOperationException("Remove not supported");
		}
	}

	protected class InputProxyConnection extends ProxyConnection
	{
		public InputProxyConnection(int index)
		{
			super(index);
		}	

		@Override
		/*@ pure nullable @*/ public Class<?> getType()
		{
			if (m_pushable != null)
			{
				return m_pushable.getType();
			}
			return null;
		}
	}

	protected class OutputProxyConnection extends ProxyConnection
	{
		public OutputProxyConnection(int index)
		{
			super(index);
		}	

		@Override
		/*@ pure nullable @*/ public Class<?> getType()
		{
			if (m_pullable != null)
			{
				return m_pullable.getType();
			}
			return null;
		}

		@Override
		public void push(Object o) 
		{
			m_pushable.push(o);
		}
	}

	@Override
	public CircuitConnection getInputConnection(int index) 
	{
		try
		{
			return m_inputPlaceholders[index].m_pullable;
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public CircuitConnection getOutputConnection(int index) 
	{
		try
		{
			return m_outputPlaceholders[index].m_pushable;
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Override
	public Object print(ObjectPrinter<?> printer) throws PrintException
	{
		return print(printer, new ArrayList<Processor>(m_innerProcessors.size()));
	}

	Object print(ObjectPrinter<?> printer, List<Processor> proc_list) throws PrintException
	{
		List<ProcessorConnection> connections = new ArrayList<ProcessorConnection>();
		List<Object> printed_procs = new ArrayList<Object>(m_innerProcessors.size());
		Map<Processor,Integer> positions = new HashMap<Processor,Integer>();
		{
			int i = 0;
			for (Processor proc : m_innerProcessors)
			{
				proc_list.add(proc);
				printed_procs.add(printer.print(proc));
				positions.put(proc, i);
				i++;
			}
		}
		for (int i = 0; i < proc_list.size(); i++)
		{
			Processor proc = proc_list.get(i);
			for (int j = 0; j < proc.getInputArity(); j++)
			{
				Pullable pl = (Pullable) proc.getInputConnection(j);
				if (pl == null || pl instanceof InputProxyConnection)
				{
					// We handle ProxyConnections later
					continue;
				}
				Processor proc_up = pl.getObject();
				int src_index = positions.get(proc_up);
				ProcessorConnection pc = new ProcessorConnection(src_index, pl.getIndex(), i, j);
				connections.add(pc);
			}
		}
		for (int i = 0; i < m_inputPlaceholders.length; i++)
		{
			InputProxyConnection ipc = m_inputPlaceholders[i];
			Pushable ph_dest = ipc.getPushable();
			if (ph_dest == null)
			{
				continue;
			}
			Processor proc_dest = ph_dest.getObject();
			ProcessorConnection pc = new ProcessorConnection(-1, i, positions.get(proc_dest), ph_dest.getIndex());
			connections.add(pc);
		}
		for (int i = 0; i < m_outputPlaceholders.length; i++)
		{
			OutputProxyConnection opc = m_outputPlaceholders[i];
			Pullable pl_dest = opc.getPullable();
			if (pl_dest == null)
			{
				continue;
			}
			Processor proc_dest = pl_dest.getObject();
			if (proc_dest == null)
			{
				continue;
			}
			ProcessorConnection pc = new ProcessorConnection(positions.get(proc_dest), pl_dest.getIndex(), -1, i);
			connections.add(pc);
		}
		List<Integer> arity = new ArrayList<Integer>(2);
		arity.add(m_inputPlaceholders.length);
		arity.add(m_outputPlaceholders.length);
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(s_arityKey, arity);
		map.put(s_processorsKey, printed_procs);
		map.put(s_connectionsKey, connections);
		map.put(s_contextKey, m_context);
		return map;
	}

	@SuppressWarnings("unchecked")
	@Override
	public Object read(ObjectReader<?> reader, Object o) throws ReadException
	{
		Object r_o = reader.read(o);
		if (!(r_o instanceof Map))
		{
			throw new ReadException("Unexpected object type");
		}
		Map<?,?> map = (Map<?,?>) r_o;
		if (!map.containsKey(s_processorsKey) || !map.containsKey(s_connectionsKey) ||
				!map.containsKey(s_arityKey) || !map.containsKey(s_contextKey))
		{
			throw new ReadException("Unexpected map format");
		}
		try
		{
			List<Integer> arity_list = (List<Integer>) map.get(s_arityKey);
			List<Processor> proc_list = (List<Processor>) map.get(s_processorsKey);
			List<ProcessorConnection> connections = (List<ProcessorConnection>) map.get(s_connectionsKey);
			Context context = (Context) map.get(s_contextKey);
			if (arity_list == null || proc_list == null || connections == null || context == null)
			{
				throw new ReadException("One of the deserialized elements is null");
			}
			GroupProcessor gp = getInstance(arity_list.get(0), arity_list.get(1));
			gp.m_innerProcessors.addAll(proc_list);
			for (ProcessorConnection pc : connections)
			{
				if (pc.m_sourceId == -1)
				{
					Processor p_dest = getOrNull(proc_list, pc.m_destinationId);
					if (p_dest == null)
					{
						throw new ReadException("Cannot find deserialized processor inside group");
					}
					gp.associateInput(pc.m_sourceIndex, p_dest, pc.m_destinationIndex);
				}
				else if (pc.m_destinationId == -1)
				{
					Processor p_src = getOrNull(proc_list, pc.m_sourceId);
					if (p_src == null)
					{
						throw new ReadException("Cannot find deserialized processor inside group");
					}
					gp.associateOutput(pc.m_sourceIndex, p_src, pc.m_destinationIndex);
				}
				else
				{
					Processor p1 = getOrNull(proc_list, pc.m_sourceId);
					Processor p2 = getOrNull(proc_list, pc.m_destinationId);
					if (p1 == null || p2 == null)
					{
						throw new ReadException("Cannot find deserialized processor inside group");
					}
					Connector.connect(p1, pc.m_sourceIndex, p2, pc.m_destinationIndex);					
				}
			}
			gp.m_context.putAll(context);
			return gp;
		}
		catch (ClassCastException cce)
		{
			throw new ReadException(cce);
		}
	}
	
	/**
	 * Gets an instance of {@link GroupProcessor}
	 * @param in_arity The input arity of the processor
	 * @param out_arity The output arity of the processor
	 * @return A new instance
	 */
	protected GroupProcessor getInstance(int in_arity, int out_arity)
	{
		return new GroupProcessor(in_arity, out_arity);
	}
	
	/**
	 * Bound-safe element list retrieval.
	 * @param list The list
	 * @param index The index in the list
	 * @return The element at position <tt>index</tt> or <tt>null</tt> if
	 * the index is out of bounds
	 */
	protected static Processor getOrNull(List<Processor> list, int index)
	{
		try
		{
			return list.get(index);
		}
		catch (IndexOutOfBoundsException e)
		{
			return null;
		}
	}

	/**
	 * Auxiliary object representing the connection of a processor's output
	 * pipe to the input pipe of another. It is used during the serialization
	 * of a group.
	 */
	protected static class ProcessorConnection implements Printable, Readable
	{
		int m_sourceId;

		int m_sourceIndex;

		int m_destinationId;

		int m_destinationIndex;

		public ProcessorConnection(int src_id, int src_index, int dst_id, int dst_index)
		{
			super();
			m_sourceId = src_id;
			m_sourceIndex = src_index;
			m_destinationId = dst_id;
			m_destinationIndex = dst_index;
		}

		public static ProcessorConnection readState(Object o) throws ReadException 
		{
			try
			{
				@SuppressWarnings("unchecked")
				List<Integer> list = (List<Integer>) o;
				return new ProcessorConnection(list.get(0), list.get(1), list.get(2), list.get(3));
			}
			catch (ClassCastException cce)
			{
				throw new ReadException(cce);
			}
			catch (IndexOutOfBoundsException cce)
			{
				throw new ReadException(cce);
			}
		}

		public List<Integer> printState() throws PrintException
		{
			List<Integer> list = new ArrayList<Integer>(4);
			list.add(m_sourceId);
			list.add(m_sourceIndex);
			list.add(m_destinationId);
			list.add(m_destinationIndex);
			return list;
		}

		@Override
		public ProcessorConnection read(ObjectReader<?> reader, Object o) throws ReadException 
		{
			Object r_o = reader.read(o);
			return readState(r_o);
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException 
		{
			return printer.print(printState());
		}
	}
	
	@Override
	/*@ pure null @*/ public Queryable getQueryable()
	{
		// TODO
		return null;
	}
}