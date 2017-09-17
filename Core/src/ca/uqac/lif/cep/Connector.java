/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

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

import java.util.Set;

/**
 * Provides a number of convenient methods for connecting the outputs of
 * processors to the inputs of other processors.
 * <p>
 * Methods provided by the <code>Connector</code> class are called
 * <code>connect()</code> and have various signatures. Their return value
 * typically consists of the <em>last</em> processor of the chain given
 * as an argument. This means that nested calls to <code>connect()</code>
 * are possible to form a complex chain of processors in one pass, e.g.
 * <pre>
 * Processor p = Connector.connect(
 *   new QueueSource(2, 1),
 *   Connector.connect(new QueueSource(1, 1), new Addition(), 0, 0),
 *   0, 1);
 * </pre>
 * <p>
 * In the previous example, the inner call to <code>connect()</code>
 * links output 0 of a <code>QueueSource</code> to input 0 of an
 * <code>Addition</code> processor; this partially-connected
 * <code>Addition</code> is the return value of this method. It is then used
 * in the outer call, where another <code>QueueSource</code> is linked
 * to its input 1. This fully-connected <code>Addition</code> is what is
 * put into variable <code>p</code>.
 * <p>
 * If you use lots of calls to <code>Connector.connect</code>, you may
 * consider writing:
 * <pre>
 * static import Connector.connect;
 * </pre>
 * in the beginning of your file, so you can simply write <code>connect</code>
 * instead of <code>Connector.connect</code> every time.
 * @author sylvain
 *
 */
public class Connector
{
	/**
	 * Whether the connector checks that the input-output types of the
	 * processor it connects are compatible.
	 */
	public static final transient boolean s_checkForTypes = true;

	/**
	 * Whether the connector checks that the processors are connected
	 * using in/out indexes within the bounds of their arity
	 */
	public static final transient boolean s_checkForBounds = false;

	/**
	 * Constant used to replace the value 0 when referring to
	 * a processor's unique input
	 */
	public static final int INPUT = 0;

	/**
	 * Constant used to replace the value 0 when referring to
	 * a processor's unique output
	 */
	public static final int OUTPUT = 0;

	/**
	 * Constant used to replace the value 0 when referring to
	 * a processor's first input or output
	 */
	public static final int LEFT = 0;

	/**
	 * Constant used to replace the value 0 when referring to
	 * a processor's first input or output
	 */
	public static final int TOP = 0;

	/**
	 * Constant used to replace the value 1 when referring to
	 * a processor's first input or output
	 */
	public static final int RIGHT = 1;

	/**
	 * Constant used to replace the value 1 when referring to
	 * a processor's first input or output
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
	 * Connects the <i>i</i>-th output of <tt>p1</tt> to the
	 * <i>j</i>-th input of <tt>p2</tt>
	 * @param p1 The first processor
	 * @param p2 The second processor
	 * @param i The output number of the first processor
	 * @param j The input number of the second processor
	 * @return A reference to processor p2
	 * @throws ConnectorException If the input/output types of the processors
	 *   to connect are incompatible
	 */
	public static synchronized Processor connect(Processor p1, Processor p2, int i, int j) throws ConnectorException
	{
		// First check for type compatibility
		if (s_checkForTypes)
		{
			// This will throw an exception if the connection is impossible
			checkForException(p1, p2, i, j);
		}
		if (p1 == p2)
		{
			// This is weird: you try to connect a processor to itself
			throw new SelfLoopException(p1, p2, i, j);
		}
		// Pull
		try
		{
			Pullable p1_out = p1.getPullableOutput(i);
			p2.setPullableInput(j, p1_out);
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
		catch (UnsupportedOperationException e)
		{
			// Same as above
		}
		return p2;
	}

	/**
	 * Connects the <i>i</i>-th output of <tt>p1</tt> to the
	 * <i>j</i>-th input of <tt>p2</tt>
	 * @param p1 The first processor
	 * @param p2 The second processor
	 * @param i The output number of the first processor
	 * @param j The input number of the second processor
	 * @return A reference to processor p2
	 * @throws ConnectorException If the input/output types of the processors
	 *   to connect are incompatible
	 */
	public static synchronized Processor connect(Processor p1, int i, Processor p2, int j) throws ConnectorException
	{
		return connect(p1, p2, i, j);
	}

	/**
	 * Connects three processors, by associating the (first) output of <tt>p1</tt>
	 * and <tt>p2</tt> respectively to the first and second input of <tt>p3</tt>
	 * @param p1 The first processor
	 * @param p2 The second processor
	 * @param p3 The third processor
	 * @return A reference to processor p3
	 * @throws ConnectorException If the input/output types of the processors
	 *   to connect are incompatible
	 */
	public static synchronized Processor connectFork(Processor p1, Processor p2, Processor p3) throws ConnectorException
	{
		connect(p1, p3, 0, 0);
		connect(p2, p3, 0, 1);
		return p3;
	}

	/**
	 * Connects a chain of processors, by associating the outputs of one
	 * to the inputs of the next. The output arity of the first must match
	 * that input arity of the next one. In the case the arity is greater
	 * than 1, the <i>i</i>-th output is linked to the <i>i</i>-th input.
	 * @param procs The list of processors
	 * @return The last processor of the chain
	 * @throws ConnectorException If the input/output types of the processors
	 *   to connect are incompatible
	 */
	public static synchronized Processor connect(Processor ... procs) throws ConnectorException
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
				connect(p1, p2, i, i);
			}
		}
		return procs[procs.length - 1];
	}

	/**
	 * Checks if the <i>i</i>-th output of processor <code>p1</code> has a
	 * declared type compatible with the <i>j</i>-th input of processor
	 * <code>p2</code>
	 * @param p1 The first processor
	 * @param p2 The second processor
	 * @param i The index of the output on the first processor
	 * @param j The index of the input on the second processor
	 * @return true if the types are compatible, false otherwise
	 */
	@SuppressWarnings("squid:S1166")
	public static boolean isCompatible(Processor p1, Processor p2, int i, int j)
	{
		try
		{
			checkForException(p1, p2, i, j);
		}
		catch (ConnectorException e)
		{
			return false;
		}
		return true;
	}

	/**
	 * Checks if the <i>i</i>-th output of processor <code>p1</code> has a
	 * declared type compatible with the <i>j</i>-th input of processor
	 * <code>p2</code>, and throws an appropriate exception if not
	 * @param p1 The first processor
	 * @param p2 The second processor
	 * @param i The index of the output on the first processor
	 * @param j The index of the input on the second processor
	 * @throws ConnectorException An exception describing why the connection
	 *   cannot be mande
	 */
	@SuppressWarnings("unused")
	protected static void checkForException(Processor p1, Processor p2, int i, int j) throws ConnectorException
	{
		Class<?> out_class = p1.getOutputType(i);
		if (s_checkForBounds && out_class == null)
		{
			// p1 has no output, so how would you connect it to p2?
			throw new IndexOutOfBoundsException(p1, p2, i, j);
		}
		if (out_class != null && out_class.equals(Variant.class))
		{
			// Skip type checking
			return;
		}
		/*@NotNull*/ Set<Class<?>> in_classes = p2.getInputType(j);
		if (in_classes.isEmpty())
		{
			if (s_checkForBounds)
			{
				// p2 has no input, so how would you connect it to p1?
				throw new IndexOutOfBoundsException(p1, p2, i, j);
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
			if (in_class.equals(Variant.class) || in_class.isAssignableFrom(out_class) || in_class.equals(Object.class))
			{
				// Found a compatible in/out pair of types: return without exception
				return;
			}
		}
		throw new IncompatibleTypesException(p1, p2, i, j);
	}

	/**
	 * Exception thrown when a problem occurs when connecting two
	 * processors
	 */
	public static class ConnectorException extends Exception
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		protected Processor m_source;

		protected Processor m_destination;

		protected int m_sourceIndex;

		protected int m_destinationIndex;

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
	 * Exception thrown when two processors with incompatible
	 * input/output types are attempted to be connected
	 */
	public static class IncompatibleTypesException extends ConnectorException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		IncompatibleTypesException(Processor source, Processor destination, int i, int j)
		{
			super(source, destination, i, j);
		}

		@Override
		public String getMessage()
		{
			StringBuilder out = new StringBuilder();
			out.append("Cannot connect output ").append(m_sourceIndex).append(" of ").append(m_source).append(" to input ").append(m_destinationIndex).append(" of ").append(m_destination).append(": incompatible types");
			return out.toString();
		}
	}

	/**
	 * Exception thrown when the connector is asked to pipe something
	 * to a nonexistent input or output
	 */
	public static class IndexOutOfBoundsException extends ConnectorException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		IndexOutOfBoundsException(Processor source, Processor destination, int i, int j)
		{
			super(source, destination, i, j);
		}

		@Override
		public String getMessage()
		{
			StringBuilder out = new StringBuilder();
			out.append("Cannot connect output ").append(m_sourceIndex).append(" of ").append(m_source).append(" to input ").append(m_destinationIndex).append(" of ").append(m_destination).append(": index out of bounds");
			return out.toString();
		}
	}
	
	/**
	 * Exception thrown when trying to connect the output of a processor to
	 * its own input
	 */
	public static class SelfLoopException extends ConnectorException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		SelfLoopException(Processor source, Processor destination, int i, int j)
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
	 * Empty class representing the fact that the output type of a processor
	 * may vary
	 */
	public static final class Variant
	{
		public static final Variant instance = new Variant();

		private Variant()
		{
			super();
		}

	}
}
