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
	 * @param o The event. Although you can technically push <code>null</code>,
	 *   the behaviour in this case is undefined. It <code>may</code> be
	 *   interpreted as if you are passing no event.
	 * @return The same instance of pushable. This is done to allow chain
	 *   calls to {@link Pushable} objects, e.g.
	 *   <code>p.push(o1).push(o2)</code>.
	 */
	public Pushable push(Object o);
	
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
	 * afterwards should return immediately. For a non-blocking
	 * pushable, this is the opposite: the call to 
	 * {@link #push(Object) push()} should return more or less
	 * immediately, but the call to this method will not return until
	 * the push operation is finished.
	 */
	public void waitFor();
}
