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
	 * The "next" status of the pullable. Indicates whether a new output event
	 * is available (i.e. can be "pulled").
	 * <ul>
	 * <li><code>YES</code> indicates that a new event can be pulled right now,
	 *   using either {@link #pullSoft()} or {@link #pull()}</li>
	 * <li><code>NO</code> indicates that no event is available, and will
	 *   ever be. Receiving <code>NO</code> generally indicates that the
	 *   end of the (output) trace has been reached</li>
	 * <li><code>MAYBE</code> indicates that no event is available, but that
	 *   keeping on pulling <em>may </em>produce an event in the future. This
	 *   value is only returned by {@link #hasNextSoft()}.</li>
	 * </ul>
	 * 
	 * @author Sylvain Hallé
	 *
	 */
	public static enum NextStatus {YES, NO, MAYBE};
	
	/**
	 * Number of times the {@link #hasNext()} method tries to produce an
	 * output from the input before giving up. While in theory, the method
	 * tries "as long as necessary", in practice a bound was put on the
	 * number of attempts as a safeguard to avoid infinite loops.
	 */
	public static final int s_maxRetries = 10000000;
	
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
	 * <li>Otherwise, the method will keep calling {@link #hasNextHard} on
	 * the inputs as long as they don't answer "no", and will try to produce
	 * an output event until one is produced.</li>
	 * <li>To avoid infinite looping, the method eventually gives up (and
	 * answers "no") after some maximum number of repetitions is reached. This
	 * is configured by the static field {@link #s_maxRetries}.
	 * </ul>
	 * @return Whether a next event exists
	 */
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
}
