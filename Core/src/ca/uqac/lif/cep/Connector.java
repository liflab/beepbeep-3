/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * Provides a number of convenient methods for connecting the outputs of
 * processors to the inputs of other processors.
 * 
 * Methods provided by the `Connector` class are called `connect()` and have
 * various signatures. Their return value typically consists of the
 * <em>last</em> processor of the chain given as an argument. This means that
 * nested calls to `connect()` are possible to form a complex chain of
 * processors in one pass, e.g. ``` java Processor p = Connector.connect( new
 * QueueSource(2, 1), Connector.connect(new QueueSource(1, 1), new Addition(),
 * 0, 0), 0, 1); ```
 * 
 * In the previous example, the inner call to <code>connect()</code> links
 * output 0 of a <code>QueueSource</code> to input 0 of an `Addition` processor;
 * this partially-connected `Addition` is the return value of this method. It is
 * then used in the outer call, where another `QueueSource` is linked to its
 * input 1. This fully-connected `Addition` is what is put into variable `p`.
 * 
 * If you use lots of calls to `Connector.connect`, you may consider writing:
 * ``` java static import Connector.connect; ``` in the beginning of your file,
 * so you can simply write `connect` instead of `Connector.connect` every time.
 * 
 * @author Sylvain Hallé
 * @since 0.1
 *
 */
public class Connector
{
  /**
   * Whether the connector checks that the input-output types of the processor it
   * connects are compatible.
   */
  public static final boolean s_checkForTypes = true;

  /**
   * Whether the connector checks that the processors are connected using in/out
   * indexes within the bounds of their arity
   */
  public static final boolean s_checkForBounds = false;

  /**
   * Constant used to replace the value 0 when referring to a processor's unique
   * input
   */
  public static final int INPUT = 0;

  /**
   * Constant used to replace the value 0 when referring to a processor's unique
   * output
   */
  public static final int OUTPUT = 0;

  /**
   * Constant used to replace the value 0 when referring to a processor's first
   * input or output
   */
  public static final int LEFT = 0;

  /**
   * Constant used to replace the value 0 when referring to a processor's first
   * input or output
   */
  public static final int TOP = 0;

  /**
   * Constant used to replace the value 1 when referring to a processor's first
   * input or output
   */
  public static final int RIGHT = 1;

  /**
   * Constant used to replace the value 1 when referring to a processor's first
   * input or output
   */
  public static final int BOTTOM = 1;

  /**
   * Utility classes should not have public constructors
   */
  private Connector()
  {
    throw new IllegalAccessError("Utility class");
  }

  /**
   * Connects the <i>i</i>-th output of <tt>p1</tt> to the <i>j</i>-th input of
   * <tt>p2</tt>
   * 
   * @param tracker
   *          An event tracker (optional)
   * @param p1
   *          The first processor
   * @param i
   *          The output number of the first processor
   * @param p2
   *          The second processor
   * @param j
   *          The input number of the second processor
   * @return A reference to processor p2
   */
  public static Processor connect(EventTracker tracker, Processor p1, int i, Processor p2, int j)
  {
    // First check for type compatibility
    if (s_checkForTypes)
    {
      // This will throw an exception if the connection is impossible
      checkForException(p1, i, p2, j);
    }
    if (p1 == p2)
    {
      // This is weird: you try to connect a processor to itself
      throw new SelfLoopException(p1, i, p2, j);
    }
    // Pull
    try
    {
      Pullable p1_out = p1.getPullableOutput(i);
      p2.setPullableInput(j, p1_out);
    }
    catch (ArrayIndexOutOfBoundsException e)
    {
      throw new Connector.IndexOutOfBoundsException(p1, i, p2, j);
    }
    catch (UnsupportedOperationException e)
    {
      // It's OK. Some processors deliberately throw this
      // exception to warn an end user that they don't have a pushable
      // or a pullable, but the connector does not care.
    }
    // Push
    try
    {
      Pushable p2_in = p2.getPushableInput(j);
      p1.setPushableOutput(i, p2_in);
    }
    catch (ArrayIndexOutOfBoundsException e)
    {
      throw new Connector.IndexOutOfBoundsException(p1, i, p2, j);
    }
    catch (UnsupportedOperationException e)
    {
      // Same as above
    }
    if (tracker != null)
    {
      tracker.setConnection(p1.getId(), i, p2.getId(), j);
    }
    return p2;
  }

  /**
   * Connects the <i>i</i>-th output of <tt>p1</tt> to the <i>j</i>-th input of
   * <tt>p2</tt>
   * 
   * @param p1
   *          The first processor
   * @param p2
   *          The second processor
   * @param i
   *          The output number of the first processor
   * @param j
   *          The input number of the second processor
   * @return A reference to processor p2
   */
  public static Processor connect(Processor p1, int i, Processor p2, int j)
  {
    return connect(null, p1, i, p2, j);
  }

  /**
   * Connects a chain of processors, by associating the outputs of one to the
   * inputs of the next. The output arity of the first must match that input arity
   * of the next one. In the case the arity is greater than 1, the <i>i</i>-th
   * output is linked to the <i>i</i>-th input.
   * 
   * @param procs
   *          The list of processors
   * @return The last processor of the chain
   */
  public static Processor connect(Processor ... procs)
  {
    return connect(null, procs);
  }

  /**
   * Connects a chain of processors, by associating the outputs of one to the
   * inputs of the next. The output arity of the first must match that input arity
   * of the next one. In the case the arity is greater than 1, the <i>i</i>-th
   * output is linked to the <i>i</i>-th input.
   * 
   * @param tracker
   *          The EventTracker
   * @param procs
   *          The list of processors
   * @return The last processor of the chain
   */
  public static Processor connect(EventTracker tracker, Processor ... procs)
  {
    if (procs.length == 1)
    {
      // If given only one processor, do nothing
      return procs[0];
    }
    for (int j = 0; j < procs.length - 1; j++)
    {
      Processor p1 = procs[j];
      Processor p2 = procs[j + 1];
      int arity = p1.getOutputArity();
      for (int i = 0; i < arity; i++)
      {
        connect(tracker, p1, i, p2, i);
      }
    }
    return procs[procs.length - 1];
  }

  /**
   * Checks if the <i>i</i>-th output of processor <code>p1</code> has a declared
   * type compatible with the <i>j</i>-th input of processor <code>p2</code>
   * 
   * @param p1
   *          The first processor
   * @param i
   *          The index of the output on the first processor
   * @param p2
   *          The second processor
   * @param j
   *          The index of the input on the second processor
   * @return true if the types are compatible, false otherwise
   */
  @SuppressWarnings("squid:S1166")
  public static boolean isCompatible(Processor p1, int i, Processor p2, int j)
  {
    try
    {
      checkForException(p1, i, p2, j);
    }
    catch (ConnectorException e)
    {
      return false;
    }
    return true;
  }

  /**
   * Checks if the <i>i</i>-th output of processor <code>p1</code> has a declared
   * type compatible with the <i>j</i>-th input of processor <code>p2</code>, and
   * throws an appropriate exception if not
   * 
   * @param p1
   *          The first processor
   * @param i
   *          The index of the output on the first processor
   * @param p2
   *          The second processor
   * @param j
   *          The index of the input on the second processor
   */
  @SuppressWarnings("unused")
  protected static void checkForException(Processor p1, int i, Processor p2, int j)
  {
    try
    {
      Class<?> out_class = p1.getOutputType(i);
      if (s_checkForBounds && out_class == null)
      {
        // p1 has no output, so how would you connect it to p2?
        throw new IndexOutOfBoundsException(p1, i, p2, j);
      }
      if (out_class != null && out_class.equals(Variant.class))
      {
        // Skip type checking
        return;
      }
      /* @NotNull */ Set<Class<?>> in_classes = p2.getInputType(j);
      if (in_classes.isEmpty())
      {
        if (s_checkForBounds)
        {
          // p2 has no input, so how would you connect it to p1?
          throw new IndexOutOfBoundsException(p1, i, p2, j);
        }
        else
        {
          // We don't mind that we connect an output to something
          // that has no input
          return;
        }
      }
      for (Class<?> in_class : in_classes)
      {
        if (in_class.equals(Variant.class) || in_class.isAssignableFrom(out_class)
            || in_class.equals(Object.class))
        {
          // Found a compatible in/out pair of types: return without exception
          return;
        }
      }
      throw new IncompatibleTypesException(p1, i, p2, j);
    }
    catch (ArrayIndexOutOfBoundsException e)
    {
      throw new IndexOutOfBoundsException(p1, i, p2, j);
    }
  }
  
  /**
   * Returns the set of connections associated to a processor
   * @param p The processor
   * @return The set of collections
   * @since 0.10.2
   */
  public static Collection<Connection> getConnections(Processor p)
  {
    Set<Connection> connections = new HashSet<Connection>();
    int p_id = p.getId();
    for (int i = 0; i < p.getInputArity(); i++)
    {
      Pullable pl = p.getPullableInput(i);
      if (pl == null)
      {
        continue;
      }
      Processor d_p = pl.getProcessor();
      if (d_p == null)
      {
        continue;
      }
      connections.add(new Connection(d_p.getId(), pl.getPosition(), p_id, i));
    }
    for (int i = 0; i < p.getOutputArity(); i++)
    {
      Pushable ps = p.getPushableOutput(i);
      if (ps == null)
      {
        continue;
      }
      Processor d_p = ps.getProcessor();
      if (d_p == null)
      {
        continue;
      }
      connections.add(new Connection(p_id, i, d_p.getId(), ps.getPosition()));
    }
    return connections;
  }

  /**
   * Exception thrown when a problem occurs when connecting two processors
   */
  public static class ConnectorException extends RuntimeException
  {
    /**
     * Dummy UID
     */
    private static final long serialVersionUID = 1L;

    /**
     * The processor at the source of the connection
     */
    protected final transient Processor m_source;

    /**
     * The processor at the destination of the connection
     */
    protected final transient Processor m_destination;

    /**
     * The index of the stream in the source processor
     */
    protected final int m_sourceIndex;

    /**
     * The index of the stream in the destination processor
     */
    protected final int m_destinationIndex;

    ConnectorException(Processor source, Processor destination, int i, int j)
    {
      super();
      m_source = source;
      m_destination = destination;
      m_sourceIndex = i;
      m_destinationIndex = j;
    }
  }

  /**
   * Exception thrown when two processors with incompatible input/output types are
   * attempted to be connected
   */
  public static class IncompatibleTypesException extends ConnectorException
  {
    /**
     * Dummy UID
     */
    private static final long serialVersionUID = 1L;

    IncompatibleTypesException(Processor source, int i, Processor destination, int j)
    {
      super(source, destination, i, j);
    }

    @Override
    public String getMessage()
    {
      StringBuilder out = new StringBuilder();
      out.append("Cannot connect output ").append(m_sourceIndex).append(" of ").append(m_source)
          .append(" to input ").append(m_destinationIndex).append(" of ").append(m_destination)
          .append(": incompatible types");
      return out.toString();
    }
  }

  /**
   * Exception thrown when the connector is asked to pipe something to a
   * nonexistent input or output
   */
  public static class IndexOutOfBoundsException extends ConnectorException
  {
    /**
     * Dummy UID
     */
    private static final long serialVersionUID = 1L;

    IndexOutOfBoundsException(Processor source, int i, Processor destination, int j)
    {
      super(source, destination, i, j);
    }

    @Override
    public String getMessage()
    {
      StringBuilder out = new StringBuilder();
      out.append("Cannot connect output ").append(m_sourceIndex).append(" of ").append(m_source)
          .append(" to input ").append(m_destinationIndex).append(" of ").append(m_destination)
          .append(": index out of bounds");
      return out.toString();
    }
  }

  /**
   * Exception thrown when trying to connect the output of a processor to its own
   * input
   */
  public static class SelfLoopException extends ConnectorException
  {
    /**
     * Dummy UID
     */
    private static final long serialVersionUID = 1L;

    SelfLoopException(Processor source, int i, Processor destination, int j)
    {
      super(source, destination, i, j);
    }

    @Override
    public String getMessage()
    {
      StringBuilder out = new StringBuilder();
      out.append("Trying to connect processor #").append(m_source.getId()).append(" to itself");
      return out.toString();
    }
  }

  /**
   * Empty class representing the fact that the output type of a processor may
   * vary
   */
  public static final class Variant
  {
    /**
     * A single visible instance of the Variant class
     */
    public static final Variant instance = new Variant();

    /**
     * Empty constructor
     */
    private Variant()
    {
      super();
    }
  }
  
  /**
   * Represents a connection between two pipes.
   * @since 0.10.2
   */
  public static class Connection
  {
    /**
     * The ID of the source processor
     */
    protected int m_sourceProcessorId;
    
    /**
     * The number of the source pipe
     */
    protected int m_sourcePipeNumber;
    
    /**
     * The ID of the destination processor
     */
    protected int m_destinationProcessorId;
    
    /**
     * The number of the destination pipe
     */
    protected int m_destinationPipeNumber;
    
    /**
     * Empty constructor
     */
    protected Connection()
    {
      this(-1, -1, -1, -1);
    }
    
    /**
     * Creates a new connection
     * @param src_id The ID of the source processor
     * @param src_pipe The number of the source pipe
     * @param dest_id The ID of the destination processor
     * @param dest_pipe The number of the destination pipe
     */
    public Connection(int src_id, int src_pipe, int dest_id, int dest_pipe)
    {
      super();
      m_sourceProcessorId = src_id;
      m_destinationProcessorId = dest_id;
      m_sourcePipeNumber = src_pipe;
      m_destinationPipeNumber = dest_pipe;
    }
    
    @Override
    public String toString()
    {
      return m_sourceProcessorId + "#" + m_sourcePipeNumber + "->"
          + m_destinationProcessorId + "#" + m_destinationPipeNumber;
    }
    
    @Override
    public int hashCode()
    {
      return m_sourceProcessorId * m_sourcePipeNumber
          + m_destinationProcessorId * m_destinationPipeNumber;
    }
    
    @Override
    public boolean equals(Object o)
    {
      if (o == null || !(o instanceof Connection))
      {
        return false;
      }
      Connection c = (Connection) o;
      return c.m_sourcePipeNumber == m_sourcePipeNumber
          && c.m_destinationPipeNumber == m_destinationPipeNumber
          && c.m_sourceProcessorId == m_sourceProcessorId
          && c.m_destinationProcessorId == m_destinationProcessorId;
    }
  }
}
