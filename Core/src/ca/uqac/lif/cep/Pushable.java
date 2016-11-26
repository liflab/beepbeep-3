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

/**
 * Gives events to some of a processor's input. Interface {@link Pushable}
 * is the opposite of {@link Pullable}: rather than querying events form
 * a processor's output (i.e. "pulling"), it gives events to a processor's
 * input. This has for effect of triggering the processor's computation
 * and "pushing" results (if any) to the processor's output.
 * <p>
 * If a processor is of input arity <i>n</i>, there exist <i>n</i> distinct
 * {@link Pullable}s: one for each input trace.
 * 
 * @author Sylvain Hallé
 *
 */
public interface Pushable
{
	/**
	 * Pushes an event into one of the processor's input trace.
	 * Contrarily to {@link #pushFast(Object)}, this method <em>must</em>
	 * return only when the push operation is completely done. Calling
	 * {@link #waitFor()} afterwards must <em>not</em> be necessary.
	 * @param o The event. Although you can technically push <code>null</code>,
	 *   the behaviour in this case is undefined. It <code>may</code> be
	 *   interpreted as if you are passing no event.
	 * @return The same instance of pushable. This is done to allow chain
	 *   calls to {@link Pushable} objects, e.g.
	 *   <code>p.push(o1).push(o2)</code>.
	 */
	public Pushable push(Object o);
	
	/**
	 * Pushes an event into one of the processor's input trace, but
	 * does not wait for the push operation to terminate. In other words,
	 * this is a non-blocking call to <code>push()</code> that returns
	 * control to the caller immediately.
	 * In order to resynchronize the caller with the result of the push
	 * operation, one must call {@link #waitFor()}.
	 * <p>
	 * Some implementations of this interface do not implement non-blocking
	 * calls; in such a case, a call to {@link #pushFast() pushFast()} will
	 * be identical to a call to {@link #push(Object) push()}, and
	 * calling {@link #waitFor()} will return immediately.
	 * @param o The event. Although you can technically push <code>null</code>,
	 *   the behaviour in this case is undefined. It <code>may</code> be
	 *   interpreted as if you are passing no event.
	 * @return The same instance of pushable. This is done to allow chain
	 *   calls to {@link Pushable} objects, e.g.
	 *   <code>p.push(o1).push(o2)</code>.
	 */
	public Pushable pushFast(Object o);

	
	/**
	 * Gets the processor instance this Pushable is linked to 
	 * @return The processor
	 */
	public Processor getProcessor();
	
	/**
	 * Gets the position this Pushable is associated to: 0 is the first input
	 * (or output), 1 the second, etc.
	 * @return The position
	 */
	public int getPosition();
	
	/**
	 * Waits until the pushable is done pushing. In the case of a
	 * blocking pushable, the call to {@link #push(Object) push()}
	 * waits for the operation to be completed; so calling this method
	 * afterwards should return immediately (as a matter of fact,
	 * calling it is even optional). For a non-blocking
	 * call (with {@link #pushFast(Object) pushFast()}, this is the opposite:
	 * the call to {@link #push(Object) push()} should return more or less
	 * immediately, but the call to this method will not return until
	 * the push operation is finished.
	 */
	public void waitFor();
	
	/**
	 * Tells this pushable that methods {@link #push(Object) push()} or
	 * {@link #pushFast(Object) pushFast()} will not be called anymore.
	 * For some types of pushables, this can be used as a cue to free
	 * some resources (such as threads). The behaviour of these two methods
	 * after <code>dispose()</code> has been called is undefined.
	 * In future versions, it is possible that an exception will
	 * be thrown in such a case.
	 */
	public void dispose();
}
