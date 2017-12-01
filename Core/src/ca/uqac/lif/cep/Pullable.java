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

import java.util.Iterator;

/**
 * Queries events on one of a processor's outputs. For a processor with
 * an output arity <i>n</i>, there exists <i>n</i> distinct pullables,
 * namely one for each output trace. Every pullable works roughly like a
 * classical <code>Iterator</code>: it is possible to check whether new
 * output events are available, and get one new output event.
 * <p>
 * However,
 * contrarily to iterators, <code>Pullable</code>s have two versions of
 * each method: a <em>soft</em> and a <em>hard</em> version.
 * <ul>
 * <li><strong>Soft</strong> methods make a single attempt at producing an
 *   output event. Since processors are connected in a chain, this generally
 *   means pulling events from the input in order to produce the output.
 *   However, if pulling the input produces no event, no output event can
 *   be produced. In such a case, {@link #hasNextSoft()} will return a special
 *   value (<code>MAYBE</code>), and {@link #pullSoft()} will return
 *   <code>null</code>. Soft methods can be seen a doing "one turn of the
 *   crank" on the whole chain of processors --whether or not this outputs
 *   something.</li>
 * <li><strong>Hard</strong> methods are actually calls to soft methods until
 *   an output event is produced: the "crank" is turned as long as necessary
 *   to produce something. This means that one call to, e.g.
 *   {@link #pull()} may consume more than one event from a processor's
 *   input. Therefore, calls to {@link #hasNext()} never return
 *   <code>MAYBE</code> (only <code>YES</code> or <code>NO</code>), and
 *   {@link #pull()} returns <code>null</code> only if no event will
 *   ever be output in the future (this occurs, for example, when pulling
 *   events from a file, and the end of the file has been reached).</li>
 * </ul>
 * <p>
 * The lifecycle of a <code>Pullable</code> object is as follows:
 * <ul>
 * <li>One obtains a reference to one of a processor's pullables. This
 *   can be done explicitly, e.g. by calling
 *   {@link Processor#getPullableOutput(int)}, or implicitly, for example
 *   through every call to {@link Connector#connect(Processor...)}.</li>
 * <li>At various moments, one calls {@link #hasNextSoft()} (or
 *   {@link #hasNext()} to check if events are available</li>
 * <li>One calls {@link #pullSoft()} (or {@link #pull()} to produce the next
 *   available output event.</li>
 * </ul>
 * <p>The Pullable interface extends the <code>Iterator</code> and
 * <code>Iterable</code> interfaces. This means that an instance of Pullable
 * can also be iterated over like this:
 * <pre>
 * Pullable p = ...;
 * for (Object o : p) {
 *   // Do something
 * }
 * </pre>
 * Note however that if <code>p</code> refers to a processor producing an
 * infinite number of events, this loop will never terminate by itself.
 * <p>
 * For the same processor, mixing calls to soft and hard methods is discouraged.
 * As a matter of fact, the Pullable's behaviour in such a situation is
 * left undefined.
 * 
 * @author Sylvain Hallé
 *
 */
public interface Pullable extends Iterator<Object>, Iterable<Object>
{
	/**
	 * Attempts to pull an event from the source. An event is returned if
	 * {@link #hasNextSoft()} returns <code>YES</code>, and <code>null</code>
	 * is returned otherwise.
	 * @return An event, or <code>null</code> if none could be retrieved
	 */
	public Object pullSoft();

	/**
	 * Attempts to pull an event from the source. An event is returned if
	 * {@link #hasNext()} returns <code>YES</code>, and <code>null</code>
	 * is returned otherwise.
	 * @return An event, or <code>null</code> if none could be retrieved
	 */
	public Object pull();

	/**
	 * Synonym of {@link #pull()}.
	 * @return An event, or <code>null</code> if none could be retrieved
	 */
	@Override
	public Object next();

	/**
	 * Determines if an event can be pulled from the output. Depending on
	 * what happens, the possible return values are:
	 * <ul>
	 * <li>If one of the inputs answers "no" when called for
	 * {@link #hasNextSoft()}, returns "no"</li>
	 * <li>If one of the inputs answers "maybe" when called for
	 * {@link #hasNextSoft()}, returns "maybe"</li>
	 * <li>If all inputs answer "yes" when called for
	 * {@link #hasNextSoft()}, but no event is produced with the given inputs,
	 * returns "maybe"</li>
	 * <li>Otherwise, returns "yes"</li>
	 * </ul>
	 * Therefore, the method is lazy in that it asks events from its input only
	 * once, and attempts to produce an output event only once.
	 * @return Whether a next event exists
	 */
	public NextStatus hasNextSoft();

	/**
	 * Determines if an event can be pulled from the output, by trying "harder"
	 * than {@link #hasNextSoft()}. Depending on
	 * what happens, the possible return values are:
	 * <ul>
	 * <li>If one of the inputs answers "no" when called for
	 * {@link #hasNextSoft()}, returns "no"</li>
	 * <li>If all inputs answer "yes" when called for
	 * {@link #hasNextSoft()}, and an event is produced with the given inputs,
	 * returns "yes"</li>
	 * <li>Otherwise, the method will keep calling {@link #hasNext()} on
	 * the inputs as long as they don't answer "no", and will try to produce
	 * an output event until one is produced.</li>
	 * <li>To avoid infinite looping, the method eventually gives up (and
	 * answers "no") after some maximum number of repetitions is reached. This
	 * is configured by the static field {@link Processor#MAX_PULL_RETRIES}.
	 * </ul>
	 * @return Whether a next event exists
	 */
	@Override
	public boolean hasNext();

	/**
	 * Gets the processor instance this Pullable is linked to
	 * @return The processor
	 */
	public Processor getProcessor();

	/**
	 * Gets the position this Pullable is associated to: 0 is the first input
	 * (or output), 1 the second, etc.
	 * @return The position
	 */
	public int getPosition();

	/**
	 * Starts the pullable. This may be useful for multi-threaded
	 * pullables.
	 */
	public void start();

	/**
	 * Stops the pullable. This may be useful for multi-threaded
	 * pullables.
	 */
	public void stop();

	/**
	 * Tells this pullable that methods {@link #pull()}, {@link #pullSoft()},
	 * {@link #hasNext()} and {@link #hasNextSoft()}
	 * will not be called anymore.
	 * For some types of pullables, this can be used as a cue to free
	 * some resources (such as threads). The behaviour of these four methods
	 * after <code>dispose()</code> has been called is undefined.
	 * In future versions, it is possible that an exception will
	 * be thrown in such a case.
	 */
	public void dispose();

	/**
	 * A runtime exception indicating that something
	 * went wrong when attempting to check if a next event exists. This
	 * happens, for example, if one of a processor's inputs it not connected
	 * to anything. Rather than throwing a {@code NullPointerException}, the
	 * issue will be wrapped within a PullableException with a better
	 * error message.
	 */
	public static class PullableException extends RuntimeException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;
		
		/**
		 * The processor to which the exception is associated (if any)
		 */
		protected final transient Processor m_processor;

		public PullableException(Throwable t)
		{
			this(t, null);
		}

		public PullableException(String message)
		{
			this(message, null);
		}
		
		public PullableException(String message, Processor p)
		{
			super(message);
			m_processor = p;
		}
		
		public PullableException(Throwable t, Processor p)
		{
			super(t);
			m_processor = p;
		}
	}
	
	/**
	 * Pullable object that throws an {@link UnsupportedOperationException}
	 * upon every call to each of its methods (except {@link #getProcessor()}).
	 * This object can be returned by
	 * processors to signal that they cannot be pulled.
	 */
	public class PullNotSupported implements Pullable
	{
		protected Processor m_processor;
		
		protected int m_position;
		
		public PullNotSupported(Processor p, int position)
		{
			super();
			m_processor = p;
			m_position = position;
		}
		
		@Override
		public Iterator<Object> iterator() 
		{
			throw new UnsupportedOperationException();
		}

		@Override
		public Object pullSoft() 
		{
			throw new UnsupportedOperationException();
		}

		@Override
		public Object pull() 
		{
			throw new UnsupportedOperationException();
		}

		@Override
		@SuppressWarnings("squid:S2272")
		public Object next() 
		{
			throw new UnsupportedOperationException();
		}

		@Override
		public NextStatus hasNextSoft() 
		{
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean hasNext() 
		{
			throw new UnsupportedOperationException();
		}

		@Override
		public Processor getProcessor() 
		{
			return m_processor;
		}

		@Override
		public int getPosition() 
		{
			return m_position;
		}

		@Override
		public void start() 
		{
			// Do nothing
		}

		@Override
		public void stop() 
		{
			// Do nothing
		}

		@Override
		public void dispose() 
		{
			// Do nothing
		}
		
		@Override
		public void remove() 
		{
			throw new UnsupportedOperationException();
		}
		
	}
}
