/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2026 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

import ca.uqac.lif.cep.Connector.SelectedInputPipe;
import ca.uqac.lif.cep.Connector.SelectedOutputPipe;
import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.SingleProcessor.InternalProcessorState;
import ca.uqac.lif.cep.tmf.Source;
import ca.uqac.lif.cep.util.Lists.MathList;
import ca.uqac.lif.petitpoucet.circuit.CompositeConnectable;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

/**
 * Encapsulates a chain of processors as if it were a single one.
 * 
 * @author Sylvain Hallé
 * @since 0.1
 */
@SuppressWarnings("squid:S2160")
public class GroupProcessor extends CompositeConnectable<Processor> implements Processor, Stateful
{
	protected final ProcessorDelegate m_delegate;

	/**
	 * The set of sources included in the group
	 */
	private HashSet<Source> m_sources;

	/**
	 * Whether to notify the QueueSource objects in the group to push an event when
	 * a call to push is made on the group
	 */
	private boolean m_notifySources = false;

	/**
	 * Creates a group processor.
	 * 
	 * @param in_arity
	 *          The input arity
	 * @param out_arity
	 *          The output arity
	 */
	public GroupProcessor(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_sources = new HashSet<Source>();
		m_delegate = new ProcessorDelegate(in_arity, out_arity, this);
	}

	/**
	 * No-args constructor assuming an input and output arity of 1.
	 */
	public GroupProcessor()
	{
		this(1, 1);
	}

	/**
	 * Sets the processor to notify the QueueSource objects in the group to push an
	 * event when a call to push is made on the group.
	 * 
	 * @param b
	 *          Set to {@code true} to notify the sources
	 * @return This group processor
	 */
	public GroupProcessor notifySources(boolean b)
	{
		m_notifySources = b;
		return this;
	}

	public void putAt(int index, SelectedInputPipe p)
	{
		associateInput(index, p.getProcessor(), p.getIndex());
	}

	public void putAt(int index, SelectedOutputPipe p)
	{
		associateOutput(index, p.getProcessor(), p.getIndex());
	}
	
	@Override
	public ProcessorDelegate delegate()
	{
		return m_delegate;
	}
	
	@Override
	/*@ non_null @*/ public final Set<Class<?>> getInputType(int index)
	{
		Set<Class<?>> classes = new HashSet<Class<?>>();
		if (index >= 0 && index < m_ins.size())
		{
			getInputTypesFor(classes, index);
		}
		return classes;
	}
	
	/**
	 * Populates the set of classes accepted by the processor for its <i>i</i>-th
	 * input.
	 * <p>
	 * By default, a processor returns the {@link Connector.Variant} type for all
	 * its inputs and all its outputs, meaning that the checking of types in
	 * {@link Connector#connect(Processor...)} will be skipped. A descendant of this
	 * class may choose to define specific types for its input and output, thereby
	 * activating runtime type checking.
	 * 
	 * @param classes
	 *          The set of to fill with classes
	 * @param index
	 *          The index of the input to query
	 */
	public void getInputTypesFor(/*@ non_null @*/ Set<Class<?>> classes, int index)
	{
		classes.add(Variant.class);
	}
	
	@Override
	public final int getId()
	{
		return m_delegate.getUniqueId();
	}
	
	@Override
	public Queue<Object> getInputQueue(int index)
	{
		return m_delegate.getInputQueue(index);
	}

	@Override
	public Queue<Object> getOutputQueue(int index)
	{
		return m_delegate.getInputQueue(index);
	}

	protected class InputOutputAssociation
	{
		/*@ non_null @*/ protected final Processor m_processor;

		/*@ non_null @*/ protected final int m_innerIndex;

		/*@ non_null @*/ protected final int m_outerIndex;

		public InputOutputAssociation(int outer_index, Processor p, int inner_index)
		{
			super();
			m_innerIndex = inner_index;
			m_outerIndex = outer_index;
			m_processor = p;
		}

		public void positive()
		{
			associateInput(m_outerIndex, m_processor, m_innerIndex);
		}

		public void negative()
		{
			associateOutput(m_outerIndex, m_processor, m_innerIndex);
		}
	}

	/**
	 * Adds a processor to the group
	 * 
	 * @param p
	 *          The processor to add
	 * @return A reference to the current group processor
	 */
	public GroupProcessor addProcessor(Processor p)
	{
		super.add(p);
		if (p instanceof Source)
		{
			m_sources.add((Source) p);
		}
		return this;
	}
	
	@Override
	public final /*@ null @*/ Object getContext(/*@ non_null @*/ String key)
	{
		return m_delegate.getContext(key);
	}

	@Override
	public /*@ non_null @*/ Context getContext()
	{
		return m_delegate.getContext();
	}

	/**
	 * Adds multiple processors to the group
	 * 
	 * @param procs
	 *          The processors to add
	 * @return A reference to the current group processor
	 */
	public GroupProcessor addProcessors(Processor ... procs)
	{
		super.add(procs);
		for (Processor p : procs)
		{
			if (p instanceof Source)
			{
				m_sources.add((Source) p);
			}
		}
		return this;
	}

	/**
	 * Declares that the first (i.e. 0-th) input of the group is linked to the
	 * first (i.e. 0-th) input of processor {@code p}.
	 * @param p The processor to connect to
	 * @return A reference to the current group processor
	 */
	public GroupProcessor associateInput(Processor p)
	{
		associateInput(0, p, 0);
		return this;
	}

	/**
	 * Declares that the first (i.e.<!-- --> 0-th) output of the group is linked
	 * to the first (i.e. 0-th) output of processor {@code p}.
	 * @param p The processor to connect to
	 * @return A reference to the current group processor
	 */
	public GroupProcessor associateOutput(Processor p)
	{
		associateOutput(0, p, 0);
		return this;
	}

	@Override
	public ProxyPushable getPushableInput(int index)
	{
		return new ProxyPushable((Pushable) m_ins.get(index), index);
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		return new ProxyPullable((Pullable) m_outs.get(index), index);
	}

	/**
	 * Sets a processor as the input 0 of the group. This method is similar to
	 * {@link #associateInput(Processor)}, except that it also automatically adds
	 * the argument to the group (something that the other method does not do).
	 * <p>
	 * This method has little interest when using BeepBeep from Java. However,
	 * in Groovy, it makes it possible to create a pipeline in a group by
	 * sparing the user from calling
	 * {@link #addProcessor(Processor) addProcessor()} and
	 * {@link #associateInput(Processor) associateInput()} separately. For
	 * instance, one could write (assuming that P1, P2 and P3 are processor
	 * instances):
	 * <pre>
	 * g = new GroupProcessor() {{
	 *   in(P1) | P2 | out(P3)
	 * }}
	 * </pre>
	 * The single line creates the pipeline, associates P1 as the input of the
	 * group, P3 as its output, and automatically adds P1, P2 and P3 to the
	 * group (that later task is taken care of by {@link #out(Processor)}.
	 * 
	 * @param p The processor to set as the input of the group
	 * @return That processor
	 * @since 0.11.3
	 */
	public Processor in(Processor p)
	{
		addProcessor(p);
		associateInput(p);
		return p;
	}

	/**
	 * Sets a processor as the output 0 of the group, and crawls the pipeline
	 * backwards from that processor to add all other processors encountered
	 * along the way.
	 * <p>
	 * This method has little interest when using BeepBeep from Java. However,
	 * in Groovy, it makes it possible to create a pipeline in a group by
	 * sparing the user from calling
	 * {@link #addProcessor(Processor) addProcessor()} and
	 * {@link #associateInput(Processor) associateOutput()} separately. For
	 * instance, one could write (assuming that P1, P2 and P3 are processor
	 * instances):
	 * <pre>
	 * g = new GroupProcessor() {{
	 *   in(P1) | P2 | out(P3)
	 * }}
	 * </pre>
	 * The single line creates the pipeline, associates P1 as the input of the
	 * group, P3 as its output, and automatically adds P1, P2 and P3 to the
	 * group.
	 * <p>
	 * The reason why this method returns a {@link CallAfterConnect} object,
	 * instead of just a processor, comes from the fact that in the context of a
	 * Groovy script, method {@code out} is called <em>before</em> the processor
	 * is connected upstream to the rest of the chain (hence in the previous
	 * example, before P3 is connected to P2). Therefore, trying to
	 * harvest other processors in the group by working up the chain from
	 * {@code p}, in the context of this method, would not return anything.
	 * <p>
	 * The workaround is therefore to pass this object, which will allow the
	 * processor to be connected, and then for upstream processors to be
	 * harvested by {@link #collectProcessors(Processor)} through the call to
	 * {@link CallAfterConnect#call()}.
	 * 
	 * @param p The processor to set as the output of the group
	 * @return A {@link CallAfterConnect} object, which allows the underlying
	 * processor to be connected, and <em>then</em> for upstream processors to be
	 * harvested by {@link #collectProcessors(Processor)}.
	 * @since 0.11.3
	 */
	public CallAfterConnect out(Processor p)
	{
		addProcessor(p);
		associateOutput(p);
		return new OutputCallAfterConnect(p);
	}

	/**
	 * Sets a selected output pipe as the output 0 of the group, and crawls the pipeline
	 * backwards from that processor to add all other processors encountered
	 * along the way.
	 * @param p The selected output pipe to set as the output of the group
	 * @return A {@link CallAfterConnect} object, which allows the underlying
	 * processor to be connected, and <em>then</em> for upstream processors to be
	 * harvested by {@link #collectProcessors(Processor)}.
	 */
	public CallAfterConnect out(SelectedOutputPipe p)
	{
		addProcessor(p.getProcessor());
		associateOutput(0, p.getProcessor(), p.getIndex());
		return new OutputCallAfterConnect(p.getProcessor());
	}

	/**
	 * Sets a selected input pipe as the input 0 of the group.
	 * @param p The selected input pipe to set as the input of the group
	 * @return A {@link CallAfterConnect} object, which allows the underlying
	 * processor to be connected, and <em>then</em> for upstream processors to be
	 * harvested by {@link #collectProcessors(Processor)}.
	 */
	public CallAfterConnect out(SelectedInputPipe p)
	{
		return out(p.getProcessor());
	}

	/**
	 * Crawls the network of processors and adds to {@link #m_processors} any
	 * processor that is not already present in the list.
	 * @param start The starting point of the collection
	 */
	protected void collectProcessors(Processor start)
	{
		new CollectCrawler().crawl(start);;
	}

	/**
	 * Creates a copy of a processor.
	 * 
	 * @param p
	 *          The processor to copy. Nothing is changed on this processor.
	 * @param with_state
	 *          If set to {@code true}, the new copy has the same events in its
	 *          input/output buffers as the original. Otherwise, the queues are
	 *          empty.
	 * @return The new processor
	 */
	protected static Processor copyProcessor(Processor p, boolean with_state)
	{
		Processor clone_p = p.duplicate(with_state);
		clone_p.setContext(p.getContext());
		if (with_state)
		{
			// Put same content in input and output queues
			for (int i = 0; i < p.getInputArity(); i++)
			{
				clone_p.addToInputQueue(i, p.getInputQueue(i));
			}
			for (int i = 0; i < p.getOutputArity(); i++)
			{
				clone_p.addToOutputQueue(i, p.getOutputQueue(i));
			}
		}
		return clone_p;
	}

	@Override
	public GroupProcessor duplicate(boolean with_state)
	{
		GroupProcessor group = new GroupProcessor(getInputArity(), getOutputArity());
		duplicate(group, with_state);
		return group;
	}

	protected void duplicate(GroupProcessor group, boolean with_state)
	{
		super.duplicate(group, with_state);
		group.m_notifySources = m_notifySources;
	}



	/**
	 * A crawler that adds to the group any processor it encounters.
	 */
	protected class CollectCrawler extends PipeCrawler
	{
		@Override
		public void visit(Processor p)
		{
			if (!m_nodes.contains(p))
			{
				m_nodes.add(p);
			}
		}
	}

	@Override
	public void setContext(Context context)
	{
		m_delegate.setContext(context);
		for (Processor p : m_nodes)
		{
			p.setContext(context);
		}
	}

	@Override
	public void setContext(String key, Object value)
	{
		m_delegate.setContext(key, value);
		for (Processor p : m_nodes)
		{
			p.setContext(key, value);
		}
	}

	public class ProxyPullable implements Pullable
	{
		protected Pullable m_pullable;

		@Override
		public void remove()
		{
			// Cannot remove an event on a pullable
			throw new UnsupportedOperationException();
		}

		@Override
		public Object pullSoft()
		{
			return m_pullable.pullSoft();
		}

		@Override
		public Object pull()
		{
			return m_pullable.pull();
		}

		@Override
		public Object next()
		{
			return m_pullable.next();
		}

		@Override
		public NextStatus hasNextSoft()
		{
			return m_pullable.hasNextSoft();
		}

		@Override
		public boolean hasNext()
		{
			return m_pullable.hasNext();
		}

		@Override
		public Processor getProcessor()
		{
			return GroupProcessor.this;
		}

		@Override
		public int getPosition()
		{
			return m_position;
		}

		protected int m_position = 0;

		/**
		 * Creates a new proxy pullable
		 * @param p The pullable to create the proxy from
		 * @param position The position
		 */
		public ProxyPullable(Pullable p, int position)
		{
			super();
			m_pullable = p;
			m_position = position;
		}

		@Override
		public Iterator<Object> iterator()
		{
			return this;
		}

		@Override
		public void start()
		{
			m_pullable.start();
		}

		@Override
		public void stop()
		{
			m_pullable.stop();
		}

		@Override
		public void dispose()
		{
			m_pullable.dispose();
		}
	}

	public class ProxyPushable implements Pushable
	{
		/**
		 * The {@link Pushable} of which this one is a proxy
		 */
		private Pushable m_pushable;

		/**
		 * The position of this pushable in the group processor
		 */
		private int m_position = 0;

		/**
		 * Creates a new proxy pushable
		 * @param p The pushable to create the proxy from
		 * @param position The position
		 */
		public ProxyPushable(Pushable p, int position)
		{
			super();
			m_pushable = p;
			m_position = position;
		}

		@Override
		public Pushable push(Object o)
		{
			m_pushable.push(o);
			notifySources();
			return m_pushable;
		}

		/**
		 * Notifies each source in the group to push an event
		 */
		protected void notifySources()
		{
			if (m_notifySources)
			{
				for (Source s : m_sources)
				{
					s.push();
				}
			}
		}

		@Override
		public void notifyEndOfTrace() throws PushableException
		{
			m_delegate.notifyEndOfTrace(m_position);
			if (!m_delegate.allNotifiedEndOfTrace())
			{
				return;
			}
			// Notify the end of trace on all the inner Pushables
			for (UpstreamConnection c : m_ins)
			{
				ProxyPushable p = (ProxyPushable) c;
				p.m_pushable.notifyEndOfTrace();
			}

			// Collect from processor the events to generate for the end
			Queue<Object[]> temp_queue = new ArrayDeque<Object[]>();
			boolean outs;
			try
			{
				outs = onEndOfTrace(temp_queue);
			}
			catch (ProcessorException e)
			{
				throw new PushableException(e);
			}
			outputEvent(temp_queue, outs);

			// Notify the output pushables of the end of the trace
			for (int i = 0; i < m_outs.size(); i++)
			{
				DownstreamConnection dc = m_outputAssociations.get(i);
				Pushable p = ((Processor) dc.getObject()).getPushableOutput(dc.getIndex());
				if (p == null)
				{
					throw new PushableException("Output " + i
							+ " of this processor is connected to nothing", getProcessor());
				}
				p.notifyEndOfTrace();
			}
		}

		/**
		 * Pushes output event (if any) to the corresponding output {@link Pushable}s.
		 *
		 * @param temp_queue The queue of object fronts to push
		 * @param outs Set to {@code true} to enable the output of an event,
		 * {@code false} otherwise.
		 */
		private final void outputEvent(Queue<Object[]> temp_queue, boolean outs)
		{
			if (outs && !temp_queue.isEmpty())
			{
				for (Object[] evt : temp_queue)
				{
					if (evt != null)
					{
						for (int i = 0; i < m_outs.size(); i++)
						{
							Pushable p = (Pushable) m_outs.get(i);
							if (p == null)
							{
								throw new PushableException(
										"Output " + i + " of this processor is connected to nothing", getProcessor());
							}
							p.push(evt[i]);
						}
					}
				}
			}
		}

		@Override
		public Processor getProcessor()
		{
			return GroupProcessor.this;
		}

		@Override
		public int getPosition()
		{
			return m_position;
		}
	}

	@Override
	public void start()
	{
		for (Processor p : m_nodes)
		{
			p.start();
		}
	}

	/**
	 * Gets the processor associated to the i-th input of the group
	 * 
	 * @param index
	 *          The index
	 * @return The processor, or {@code null} if no processor is associated to this
	 *         index
	 */
	public Processor getAssociatedInput(int index)
	{
		return (Processor) m_inputAssociations.get(index).getObject();
	}

	/**
	 * Gets the index of the group's input pipe associated to the inner processor
	 * with given ID and pipe index.
	 * @param id The ID of the inner processor
	 * @param pipe_index The input pipe index of the inner processor
	 * @return The index of the group's input pipe, or -1 if no such association
	 * exists
	 */
	public int getGroupInputIndex(int id, int pipe_index)
	{
		for (int i = 0; i < m_inputAssociations.size(); i++)
		{
			UpstreamConnection uc = m_inputAssociations.get(i);
			if (((Processor) uc.getObject()).getId() == id && uc.getIndex() == pipe_index)
			{
				return i;
			}
		}
		return -1;
	}

	/**
	 * Gets the input stream index of the processor associated to the i-th
	 * input of the group.
	 * 
	 * @param index
	 *          The index
	 * @return The index, or {@code -1} if no processor is associated to this
	 *         index
	 */
	public int getAssociatedInputIndex(int index)
	{
		
		if (index < 0 || index >= m_inputAssociations.size())
		{
			return -1;
		}
		return m_inputAssociations.get(index).getIndex();
	}

	/**
	 * Gets the processor associated to the i-th output of the group
	 * 
	 * @param index
	 *          The index
	 * @return The processor, or {@code null} if no processor is associated to this
	 *         index
	 */
	public Processor getAssociatedOutput(int index)
	{
		if (index < 0 || index >= m_outputAssociations.size())
		{
			return null;
		}
		return (Processor) m_outputAssociations.get(index).getObject();
	}

	/**
	 * Gets the output stream index of the processor associated to the i-th
	 * output of the group.
	 * 
	 * @param index
	 *          The index
	 * @return The index, or {@code -1} if no processor is associated to this
	 *         index
	 */
	public int getAssociatedOutputIndex(int index)
	{
		if (index < 0 || index >= m_outputAssociations.size())
		{
			return -1;
		}
		return m_outputAssociations.get(index).getIndex();
	}

	protected boolean onEndOfTrace(Queue<Object[]> outputs)
	{
		/*
		for (int i = 0; i < getInputArity(); i++)
		{
			ProcessorAssociation pa = m_inputPullableAssociations.get(i);
			pa.m_processor.
		}
		 */
		return false;
	}

	/**
	 * @since 0.10.2
	 */
	@Override
	public Object printState()
	{
		Map<String,Object> contents = new HashMap<String,Object>();
		contents.put("in-arity", getInputArity());
		contents.put("out-arity", getOutputArity());
		contents.put("processors", m_nodes);
		contents.put("sources", m_sources);
		contents.put("notify-sources", m_notifySources);
		Set<List<Integer>> in_assocs = new HashSet<List<Integer>>();
		for (int i = 0; i < m_inputAssociations.size(); i++)
		{
			List<Integer> list = new ArrayList<Integer>(3);
			list.add(i);
			UpstreamConnection uc = m_inputAssociations.get(i);
			list.add(uc.getIndex());
			list.add(((Processor) uc.getObject()).getId());
			in_assocs.add(list);
		}
		contents.put("input-associations", in_assocs);
		Set<List<Integer>> out_assocs = new HashSet<List<Integer>>();
		for (int i = 0; i < m_inputAssociations.size(); i++)
		{
			List<Integer> list = new ArrayList<Integer>(3);
			list.add(i);
			DownstreamConnection uc = m_outputAssociations.get(i);
			list.add(uc.getIndex());
			list.add(((Processor) uc.getObject()).getId());
			in_assocs.add(list);
		}
		contents.put("output-associations", out_assocs);
		Set<Connector.Connection> connections = new HashSet<Connector.Connection>();
		for (Processor p : m_nodes)
		{
			connections.addAll(Connector.getConnections(p));
		}
		contents.put("connections", connections);
		return contents;
	}

	/**
	 * @since 0.10.2
	 */
	@SuppressWarnings("unchecked")
	@Override
	public GroupProcessor readState(Object o) throws ProcessorException
	{
		Map<String,Object> contents = (HashMap<String,Object>) o;
		// Create processor
		GroupProcessor gp = new GroupProcessor(((Number) contents.get("in-arity")).intValue(), 
				((Number) contents.get("out-arity")).intValue());
		// Add internal processors (regular and source)
		Map<Integer,Processor> procs = new HashMap<Integer,Processor>();
		for (Processor p : (List<Processor>) contents.get("processors"))
		{
			gp.addProcessor(p);
			procs.put(p.getId(), p);
		}
		for (Processor p : (Set<Processor>) contents.get("sources"))
		{
			gp.addProcessor(p);
			procs.put(p.getId(), p);
		}
		// Connect each of them according to the connections
		Set<Connector.Connection> connections = (Set<Connector.Connection>) contents.get("connections");
		for (Connector.Connection conn : connections)
		{
			Processor p1 = procs.get(conn.m_sourceProcessorId);
			Processor p2 = procs.get(conn.m_destinationProcessorId);
			if (p1 == null || p2 == null)
			{
				// Ignore
				continue;
			}
			Connector.connect(p1, conn.m_sourcePipeNumber, p2, conn.m_destinationPipeNumber);
		}
		// Associate group's inputs to processor inputs
		for (List<Integer> list : ((Set<List<Integer>>) contents.get("input-associations")))
		{
			int io_1 = list.get(0);
			int io_2 = list.get(1);
			int p_id = list.get(2);
			if (!procs.containsKey(p_id))
			{
				// Ignore
				continue;
			}
			Processor p = procs.get(p_id);
			gp.associateInput(io_1, p, io_2);
		}
		// Associate group's outputs to processor outputs
		for (List<Integer> list : ((Set<List<Integer>>) contents.get("output-associations")))
		{
			int io_1 = list.get(0);
			int io_2 = list.get(1);
			int p_id = list.get(2);
			if (!procs.containsKey(p_id))
			{
				// Ignore
				continue;
			}
			Processor p = procs.get(p_id);
			gp.associateOutput(io_1, p, io_2);
		}
		gp.m_notifySources = (Boolean) contents.get("notify-sources");
		return gp;
	}

	@Override
	public void reset()
	{
		for (Processor p : m_nodes)
		{
			p.reset();
		}
		for (Source p : m_sources)
		{
			p.reset();
		}
	}

	@Override
	public Object getState()
	{
		MathList<InternalProcessorState> group_state = new MathList<InternalProcessorState>();
		for (Processor p : m_nodes)
		{
			group_state.add(new InternalProcessorState(p));
		}
		return group_state;
	}

	/**
	 * A {@link CallAfterConnect} object that can be used to connect the
	 * underlying processor of a {@link GroupProcessor}, and then to collect all
	 * processors that are part of the group. Currently the only use of this
	 * class is to be returned by the {@link #out(Processor)} method. (And in
	 * turn, the only real use of this method is in Groovy scripts to save
	 * a few keystrokes when creating a group.)
	 * @since 0.11.4
	 */
	protected class OutputCallAfterConnect implements CallAfterConnect
	{
		/**
		 * The processor to be connected.
		 */
		private final Processor m_processor;

		/**
		 * Creates a new {@link OutputCallAfterConnect} object.
		 * @param p The processor to be connected
		 */
		public OutputCallAfterConnect(Processor p)
		{
			super();
			m_processor = p;
		}

		@Override
		public Processor getProcessor()
		{
			return m_processor;
		}

		@Override
		public void call()
		{
			collectProcessors(m_processor);
		}
	}

	@Override
	protected UpstreamConnection newInputAssociation(Processor p, int index)
	{
		return new InputAssociation(p, index);
	}

	@Override
	protected DownstreamConnection newOutputAssociation(Processor p, int index)
	{
		return new OutputAssociation(p, index);
	}
	
	protected static class OutputAssociation implements DownstreamConnection
	{
		protected final Processor m_object;
		
		protected final int m_index;
		
		public OutputAssociation(Processor p, int index)
		{
			super();
			m_object = p;
			m_index = index;
		}
		
		@Override
		public int getIndex()
		{
			return m_index;
		}

		@Override
		public Processor getObject()
		{
			return m_object;
		}
		
		@Override
		public int hashCode()
		{
			return m_object.hashCode() + m_index;
		}
		
		@Override
		public boolean equals(Object o)
		{
			if (!(o instanceof OutputAssociation))
			{
				return false;
			}
			OutputAssociation a = (OutputAssociation) o;
			return a.m_index == m_index && a.m_object.equals(m_object);
		}
	}
	
	protected static class InputAssociation implements UpstreamConnection
	{
		protected final Processor m_object;
		
		protected final int m_index;
		
		public InputAssociation(Processor p, int index)
		{
			super();
			m_object = p;
			m_index = index;
		}
		
		@Override
		public int getIndex()
		{
			return m_index;
		}

		@Override
		public Processor getObject()
		{
			return m_object;
		}
		
		@Override
		public int hashCode()
		{
			return m_object.hashCode() + m_index;
		}
		
		@Override
		public boolean equals(Object o)
		{
			if (!(o instanceof InputAssociation))
			{
				return false;
			}
			InputAssociation a = (InputAssociation) o;
			return a.m_index == m_index && a.m_object.equals(m_object);
		}
	}
}