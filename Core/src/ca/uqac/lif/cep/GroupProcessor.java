/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2022 Sylvain Hallé

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

import ca.uqac.lif.cep.tmf.Source;
import ca.uqac.lif.cep.util.Lists.MathList;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.Future;

/**
 * Encapsulates a chain of processors as if it were a single one.
 * 
 * @author Sylvain Hallé
 * @since 0.1
 */
@SuppressWarnings("squid:S2160")
public class GroupProcessor extends Processor implements Stateful
{
  /**
   * The set of processors included in the group
   */
  private List<Processor> m_processors;

  /**
   * The set of sources included in the group
   */
  private HashSet<Source> m_sources;

  /**
   * The {@link Pushable}s associated to each of the processor's input traces
   */
  private transient List<Pushable> m_inputPushables;

  /**
   * The {@link Pullable}s associated to each of the processor's output traces
   */
  private transient List<Pullable> m_outputPullables;

  /**
   * Whether to notify the QueueSource objects in the group to push an event when
   * a call to push is made on the group
   */
  private boolean m_notifySources = false;

  /**
   * A map between numbers and processor associations. An element (m,(n,p)) of
   * this map means that the <i>m</i>-th input of the group processor is in fact
   * the <i>n</i>-th input of processor <code>p</code>
   */
  private HashMap<Integer, ProcessorAssociation> m_inputPullableAssociations;

  /**
   * A map between numbers and processor associations. An element (m,(n,p)) of
   * this map means that the <i>m</i>-th output of the group processor is in fact
   * the <i>n</i>-th output of processor <code>p</code>
   */
  private HashMap<Integer, ProcessorAssociation> m_outputPushableAssociations;

  /**
   * An inner event tracker for the group
   */
  protected EventTracker m_innerTracker;

  /**
   * Crate a group processor
   * 
   * @param in_arity
   *          The input arity
   * @param out_arity
   *          The output arity
   */
  public GroupProcessor(int in_arity, int out_arity)
  {
    super(in_arity, out_arity);
    m_processors = new ArrayList<Processor>();
    m_sources = new HashSet<Source>();
    m_inputPushables = new ArrayList<Pushable>();
    m_outputPullables = new ArrayList<Pullable>();
    m_inputPullableAssociations = new HashMap<Integer, ProcessorAssociation>();
    m_outputPushableAssociations = new HashMap<Integer, ProcessorAssociation>();
    m_innerTracker = null;
  }

  /**
   * No-args constructor. Used only for serialization and deserialization.
   */
  protected GroupProcessor()
  {
    this(1, 1);
  }

  /**
   * Sets the processor to notify the QueueSource objects in the group to push an
   * event when a call to push is made on the group.
   * 
   * @param b
   *          Set to <tt>true</tt> to notify the sources
   * @return This group processor
   */
  public GroupProcessor notifySources(boolean b)
  {
    m_notifySources = b;
    return this;
  }
  
  /**
   * Gets the tracker instance for the processors contained in this group.
   * @return The tracker instance, or <tt>null</tt> if no inner tracker is set.
   * @since 0.11
   */
  /*@ pure null @*/ public EventTracker getInnerTracker()
  {
  	return m_innerTracker;
  }

  /**
   * Tuple made of a number and a processor.
   * 
   * @author Sylvain Hallé
   */
  protected static class ProcessorAssociation
  {
    /**
     * The number
     */
    int m_ioNumber;

    /**
     * The processor
     */
    Processor m_processor;

    /**
     * Create a new processor association
     * 
     * @param number
     *          The number
     * @param p
     *          The processor associated to that number
     */
    ProcessorAssociation(int number, Processor p)
    {
      super();
      m_ioNumber = number;
      m_processor = p;
    }

    /**
     * No-args constructor. Used only for serialization and deserialization.
     */
    protected ProcessorAssociation()
    {
      super();
    }
  }

  /**
   * Adds a processor to the group
   * 
   * @param p
   *          The processor to add
   * @return A reference to the current group processor
   */
  public synchronized GroupProcessor addProcessor(Processor p)
  {
    m_processors.add(p);
    if (m_innerTracker != null)
    {
    	p.setEventTracker(m_innerTracker);
    }
    if (p instanceof Source)
    {
      m_sources.add((Source) p);
    }
    return this;
  }

  /**
   * Adds multiple processors to the group
   * 
   * @param procs
   *          The processors to add
   * @return A reference to the current group processor
   */
  public synchronized GroupProcessor addProcessors(Processor ... procs)
  {
    for (Processor p : procs)
    {
      m_processors.add(p);
      if (m_innerTracker != null)
      {
      	p.setEventTracker(m_innerTracker);
      }
      if (p instanceof Source)
      {
        m_sources.add((Source) p);
      }
    }
    return this;
  }

  /**
   * Declares that the <i>i</i>-th input of the group is linked to the <i>j</i>-th
   * input of processor <code>p</code>
   * 
   * @param i
   *          The number of the input of the group
   * @param p
   *          The processor to connect to
   * @param j
   *          The number of the input of processor <code>p</code>
   * @return A reference to the current group processor
   */
  public synchronized GroupProcessor associateInput(int i, Processor p, int j)
  {
    setPushableInput(i, p.getPushableInput(j));
    setPullableInputAssociation(i, p, j);
    return this;
  }

  /**
   * Declares that the <i>i</i>-th output of the group is linked to the
   * <i>j</i>-th output of processor p
   * 
   * @param i
   *          The number of the output of the group
   * @param p
   *          The processor to connect to
   * @param j
   *          The number of the output of processor <code>p</code>
   * @return A reference to the current group processor
   */
  public synchronized GroupProcessor associateOutput(int i, Processor p, int j)
  {
    setPullableOutput(i, p.getPullableOutput(j));
    setPushableOutputAssociation(i, p, j);
    return this;
  }

  @Override
  public synchronized ProxyPushable getPushableInput(int index)
  {
    return (ProxyPushable) m_inputPushables.get(index);
  }

  @Override
  public synchronized Pullable getPullableOutput(int index)
  {
    return new ProxyPullable(m_outputPullables.get(index), index);
  }

  @Override
  public final synchronized void setPullableInput(int i, Pullable p)
  {
    ProcessorAssociation a = m_inputPullableAssociations.get(i);
    a.m_processor.setPullableInput(a.m_ioNumber, p);
  }

  public final synchronized void setPushableOutputAssociation(int i, Processor p, int j)
  {
    m_outputPushableAssociations.put(i, new GroupProcessor.ProcessorAssociation(j, p));
  }

  @Override
  public final synchronized void setPushableOutput(int i, Pushable p)
  {
    ProcessorAssociation a = m_outputPushableAssociations.get(i);
    a.m_processor.setPushableOutput(a.m_ioNumber, p);
  }

  public final synchronized void setPullableInputAssociation(int i, Processor p, int j)
  {
    m_inputPullableAssociations.put(i, new GroupProcessor.ProcessorAssociation(j, p));
  }

  /**
   * Sets an input pushable for this processor
   * @param i The position
   * @param p The pushable
   */
  public final synchronized void setPushableInput(int i, Pushable p)
  {
    if (i == m_inputPushables.size())
    {
      m_inputPushables.add(new ProxyPushable(p, i));
    }
    else
    {
      m_inputPushables.set(i, new ProxyPushable(p, i));
    }
  }

  /**
   * Sets an output pullable for this processor
   * @param i The index of the pullable
   * @param p The pullable
   */
  public final synchronized void setPullableOutput(int i, Pullable p)
  {
    if (i == m_outputPullables.size())
    {
      m_outputPullables.add(p);
    }
    else
    {
      m_outputPullables.set(i, p);
    }
  }

  @Override
  public final synchronized Pushable getPushableOutput(int index)
  {
    ProcessorAssociation a = m_outputPushableAssociations.get(index);
    if (a == null)
    {
    	return null;
    }
    return a.m_processor.getPushableOutput(a.m_ioNumber);
  }

  @Override
  public final synchronized Pullable getPullableInput(int index)
  {
    ProcessorAssociation a = m_inputPullableAssociations.get(index);
    if (a == null)
    {
    	return null;
    }
    return a.m_processor.getPullableInput(a.m_ioNumber);
  }

  /**
   * Clones the contents of the current {@link GroupProcessor} into a new group
   * 
   * @param group
   *          The {@link GroupProcessor} to clone into. When the method is called,
   *          it is expected to be empty.
   * @param with_state
   *          It set to <tt>true</tt>, each processor in the new group has the same
   *          events in its input/output buffers as in the original. Otherwise,
   *          the queues are empty.
   * @return An association between IDs and the new processors that have been put
   *         into the group
   */
  public synchronized Map<Integer, Processor> cloneInto(GroupProcessor group, boolean with_state)
  {
    super.duplicateInto(group);
    if (group.m_eventTracker != null)
    {
    	group.m_eventTracker.add(group);
    }
    group.m_notifySources = m_notifySources;
    Map<Integer, Processor> new_procs = new HashMap<Integer, Processor>();
    EventTracker new_tracker = null;
    if (m_innerTracker != null)
    {
    	new_tracker = m_innerTracker.getCopy(false);
    }
    group.m_innerTracker = new_tracker;
    Processor start = null;
    // Clone every processor of the original group
    for (Processor p : m_processors)
    {
      if (start == null && p.getOutputArity() > 0)
      {
        start = p;
      }
      Processor clone_p = copyProcessor(p, with_state);
      new_procs.put(p.getId(), clone_p);
      group.addProcessor(clone_p);
    }
    // Re-pipe the inputs and outputs like in the original group
    associateEndpoints(group, new_procs);
    // Re-pipe the internal processors like in the original group
    CopyCrawler cc = new CopyCrawler(new_procs, new_tracker);
    cc.crawl(start);
    return new_procs;
  }

  /**
   * Associates the endpoints of a new {@link GroupProcessor} like the ones in the
   * current group
   * 
   * @param group
   *          The new group
   * @param new_procs
   *          An association between processor IDs and processors
   */
  protected synchronized void associateEndpoints(GroupProcessor group,
      Map<Integer, Processor> new_procs)
  {
    // Re-pipe the inputs like in the original group
    for (Map.Entry<Integer, ProcessorAssociation> entry : m_inputPullableAssociations.entrySet())
    {
      int input_number = entry.getKey();
      ProcessorAssociation pa = entry.getValue();
      Processor clone_p = new_procs.get(pa.m_processor.getId());
      group.associateInput(input_number, clone_p, pa.m_ioNumber);
    }
    // Re-pipe the outputs like in the original group
    for (Map.Entry<Integer, ProcessorAssociation> entry : m_outputPushableAssociations.entrySet())
    {
      int output_number = entry.getKey();
      ProcessorAssociation pa = entry.getValue();
      Processor clone_p = new_procs.get(pa.m_processor.getId());
      group.associateOutput(output_number, clone_p, pa.m_ioNumber);
    }
  }

  /**
   * Creates a copy of a processor.
   * 
   * @param p
   *          The processor to copy. Nothing is changed on this processor.
   * @param with_state
   *          If set to <tt>true</tt>, the new copy has the same events in its
   *          input/output buffers as the original. Otherwise, the queues are
   *          empty.
   * @return The new processor
   */
  protected static synchronized Processor copyProcessor(Processor p, boolean with_state)
  {
    Processor clone_p = p.duplicate(with_state);
    clone_p.setContext(p.m_context);
    if (with_state)
    {
      // Put same content in input and output queues
      for (int i = 0; i < p.m_inputQueues.length; i++)
      {
        clone_p.m_inputQueues[i].addAll(p.m_inputQueues[i]);
      }
      for (int i = 0; i < p.m_outputQueues.length; i++)
      {
        clone_p.m_outputQueues[i].addAll(p.m_outputQueues[i]);
      }
    }
    return clone_p;
  }

  @Override
  public synchronized GroupProcessor duplicate(boolean with_state)
  {
    GroupProcessor group = new GroupProcessor(getInputArity(), getOutputArity());
    cloneInto(group, with_state);
    return group;
  }

  /**
   * Crawler that creates copies (clones) of whatever it encounters on its way and
   * re-pipes processors as in the original group.
   * <p>
   * <strong>Caveat emptor</strong>: the starting point of the crawl cannot be a
   * processor with output arity of 0. Otherwise, none of the processors in the
   * new group will be piped together.
   * 
   * @author Sylvain Hallé
   */
  protected static class CopyCrawler extends PipeCrawler
  {
    private final Map<Integer, Processor> m_correspondences;
    
    private final EventTracker m_tracker;

    public CopyCrawler(Map<Integer, Processor> correspondences, EventTracker tracker)
    {
      super();
      m_correspondences = new HashMap<Integer, Processor>();
      m_correspondences.putAll(correspondences);
      m_tracker = tracker;
    }

    @Override
    public synchronized void crawl(Processor start)
    {
      if (start.getOutputArity() == 0)
      {
        throw new UnsupportedOperationException(
            "A copy crawl cannot start from a processor of output arity 0.");
      }
      super.crawl(start);
    }

    @Override
    public synchronized void visit(Processor p)
    {
      int out_arity = p.getOutputArity();
      for (int i = 0; i < out_arity; i++)
      {
        Pushable push = p.getPushableOutput(i);
        if (push != null)
        {
          Processor target = push.getProcessor();
          int j = push.getPosition();
          Processor new_p;
          Processor new_target;
          synchronized (m_correspondences)
          {
            new_p = m_correspondences.get(p.getId());
            new_target = m_correspondences.get(target.getId());
          }
          if (new_p != null && new_target != null)
          {
            // new_p and new_target may be null if they refer to a processor
            // outside of the group
          	Connector.connect(m_tracker, new_p, i, new_target, j);
          }
        }
      }
    }
  }

  @Override
  public synchronized void setContext(Context context)
  {
    super.setContext(context);
    for (Processor p : m_processors)
    {
      p.setContext(context);
    }
  }

  @Override
  public synchronized void setContext(String key, Object value)
  {
    super.setContext(key, value);
    for (Processor p : m_processors)
    {
      p.setContext(key, value);
    }
  }

  public class ProxyPullable implements Pullable
  {
    protected Pullable m_pullable;

    @Override
    public synchronized void remove()
    {
      // Cannot remove an event on a pullable
      throw new UnsupportedOperationException();
    }

    @Override
    public synchronized Object pullSoft()
    {
      return m_pullable.pullSoft();
    }

    @Override
    public synchronized Object pull()
    {
      return m_pullable.pull();
    }

    @Override
    public synchronized Object next()
    {
      return m_pullable.next();
    }

    @Override
    public synchronized NextStatus hasNextSoft()
    {
      return m_pullable.hasNextSoft();
    }

    @Override
    public synchronized boolean hasNext()
    {
      return m_pullable.hasNext();
    }

    @Override
    public synchronized Processor getProcessor()
    {
      return GroupProcessor.this;
    }

    @Override
    public synchronized int getPosition()
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
      synchronized (this)
      {
        m_pullable = p;
        m_position = position;
      }
    }

    @Override
    public synchronized Iterator<Object> iterator()
    {
      return this;
    }

    @Override
    public synchronized void start()
    {
      m_pullable.start();
    }

    @Override
    public synchronized void stop()
    {
      m_pullable.stop();
    }

    @Override
    public synchronized void dispose()
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
      synchronized (this)
      {
        m_pushable = p;
        m_position = position;
      }
    }

    @Override
    public synchronized Pushable push(Object o)
    {
      m_pushable.push(o);
      notifySources();
      return m_pushable;
    }

    @Override
    public synchronized Future<Pushable> pushFast(Object o)
    {
      push(o);
      return Pushable.NULL_FUTURE;
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
      m_hasBeenNotifiedOfEndOfTrace[m_position] = true;
      if (!allNotifiedEndOfTrace())
      {
        return;
      }
      // Notify the end of trace on all the inner Pushables
      for (Pushable p : m_inputPushables)
      {
        ((ProxyPushable) p).m_pushable.notifyEndOfTrace();
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
      for (int i = 0; i < m_outputPushables.length; i++)
      {
        ProcessorAssociation pa = m_outputPushableAssociations.get(i);
        Pushable p = pa.m_processor.getPushableOutput(pa.m_ioNumber);
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
     * @param outs Set to <tt>true</tt> to enable the output of an event,
     * <tt>false</tt> otherwise.
     */
    private final void outputEvent(Queue<Object[]> temp_queue, boolean outs)
    {
      if (outs && !temp_queue.isEmpty())
      {
        for (Object[] evt : temp_queue)
        {
          if (evt != null)
          {
            for (int i = 0; i < m_outputPushables.length; i++)
            {
              Pushable p = m_outputPushables[i];
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
    public synchronized Processor getProcessor()
    {
      return GroupProcessor.this;
    }

    @Override
    public synchronized int getPosition()
    {
      return m_position;
    }
  }

  @Override
  public synchronized void start()
  {
    super.start();
    for (Processor p : m_processors)
    {
      p.start();
    }
  }

  @Override
  public synchronized void stop()
  {
    super.stop();
    for (Processor p : m_processors)
    {
      p.stop();
    }
  }

  /**
   * Gets the processor associated to the i-th input of the group
   * 
   * @param index
   *          The index
   * @return The processor, or <tt>null</tt> if no processor is associated to this
   *         index
   */
  public Processor getAssociatedInput(int index)
  {
    if (!m_inputPullableAssociations.containsKey(index))
    {
      return null;
    }
    return m_inputPullableAssociations.get(index).m_processor;
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
  	for (Map.Entry<Integer,ProcessorAssociation> e : m_inputPullableAssociations.entrySet())
  	{
  		ProcessorAssociation pa = e.getValue();
  		if (pa.m_processor.getId() == id && pa.m_ioNumber == pipe_index)
  		{
  			return e.getKey();
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
   * @return The index, or <tt>-1</tt> if no processor is associated to this
   *         index
   */
  public int getAssociatedInputIndex(int index)
  {
    if (!m_inputPullableAssociations.containsKey(index))
    {
      return -1;
    }
    return m_inputPullableAssociations.get(index).m_ioNumber;
  }
  
  /**
   * Gets the processor associated to the i-th output of the group
   * 
   * @param index
   *          The index
   * @return The processor, or <tt>null</tt> if no processor is associated to this
   *         index
   */
  public Processor getAssociatedOutput(int index)
  {
    if (!m_outputPushableAssociations.containsKey(index))
    {
      return null;
    }
    return m_outputPushableAssociations.get(index).m_processor;
  }
  
  /**
   * Gets the output stream index of the processor associated to the i-th
   * output of the group.
   * 
   * @param index
   *          The index
   * @return The index, or <tt>-1</tt> if no processor is associated to this
   *         index
   */
  public int getAssociatedOutputIndex(int index)
  {
    if (!m_outputPushableAssociations.containsKey(index))
    {
      return -1;
    }
    return m_outputPushableAssociations.get(index).m_ioNumber;
  }

  @Override
  public boolean onEndOfTrace(Queue<Object[]> outputs)
  {
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
    contents.put("processors", m_processors);
    contents.put("sources", m_sources);
    contents.put("notify-sources", m_notifySources);
    Set<List<Integer>> in_assocs = new HashSet<List<Integer>>();
    for (Map.Entry<Integer,ProcessorAssociation> entry : m_inputPullableAssociations.entrySet())
    {
      List<Integer> list = new ArrayList<Integer>(3);
      list.add(entry.getKey());
      ProcessorAssociation pa = entry.getValue();
      list.add(pa.m_ioNumber);
      list.add(pa.m_processor.getId());
      in_assocs.add(list);
    }
    contents.put("input-associations", in_assocs);
    Set<List<Integer>> out_assocs = new HashSet<List<Integer>>();
    for (Map.Entry<Integer,ProcessorAssociation> entry : m_outputPushableAssociations.entrySet())
    {
      List<Integer> list = new ArrayList<Integer>(3);
      list.add(entry.getKey());
      ProcessorAssociation pa = entry.getValue();
      list.add(pa.m_ioNumber);
      list.add(pa.m_processor.getId());
      out_assocs.add(list);
    }
    contents.put("output-associations", out_assocs);
    Set<Connector.Connection> connections = new HashSet<Connector.Connection>();
    for (Processor p : m_processors)
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
    for (Processor p : (Set<Processor>) contents.get("processors"))
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
    super.reset();
    for (Processor p : m_processors)
    {
      p.reset();
    }
    for (Source p : m_sources)
    {
      p.reset();
    }
  }

  @Override
  public final Processor setEventTracker(/*@ null @*/ EventTracker tracker)
  {
    super.setEventTracker(tracker);
    tracker.add(this);
    if (tracker != null && m_innerTracker == null)
    {
      m_innerTracker = tracker.getCopy(false);
      for (Processor p : m_processors)
      {
        p.setEventTracker(m_innerTracker);
      }
    }
    return this;
  }
  
  @Override
  public Object getState()
  {
  	MathList<InternalProcessorState> group_state = new MathList<InternalProcessorState>();
  	for (Processor p : m_processors)
  	{
  		group_state.add(new InternalProcessorState(p));
  	}
  	return group_state;
  }
}
