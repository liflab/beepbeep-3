/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

public interface Pullable
{
	public static enum NextStatus {YES, NO, MAYBE};
	
	/**
	 * Number of times the {@link #hasNext} method tries to produce an
	 * output from the input before giving up 
	 */
	public static final long s_maxRetries = 1000;
	
	/**
	 * Attempts to pull an event from the source. An event is returned if
	 * {@link #hasNext()} returns "yes", and null is returned otherwise.
	 * @return An event, or null if none could be retrieved
	 */
	public Object pull();

	/**
	 * Attempts to pull an event from the source. An event is returned if
	 * {@link #hasNextHard()} returns "yes", and null is returned otherwise.
	 * @return An event, or null if none could be retrieved
	 */
	public Object pullHard();
	
	/**
	 * Determines if an event can be pulled from the output. Depending on
	 * what happens, the possible return values are:
	 * <ul>
	 * <li>If one of the inputs answers "no" when called for
	 * {@link #hasNext()}, returns "no"</li>
	 * <li>If one of the inputs answers "maybe" when called for
	 * {@link #hasNext()}, returns "maybe"</li>
	 * <li>If all inputs answer "yes" when called for
	 * {@link #hasNext()}, but no event is produced with the given inputs,
	 * returns "maybe"</li>
	 * <li>Otherwise, returns "yes"</li>
	 * </ul>
	 * Therefore, the method is lazy in that it asks events from its input only
	 * once, and attempts to produce an output event only once.
	 * @return Whether a next event exists
	 */
	public NextStatus hasNext();

	/**
	 * Determines if an event can be pulled from the output, by trying "harder"
	 * than {@link #hasNext()}. Depending on
	 * what happens, the possible return values are:
	 * <ul>
	 * <li>If one of the inputs answers "no" when called for
	 * {@link #hasNext()}, returns "no"</li>
	 * <li>If all inputs answer "yes" when called for
	 * {@link #hasNext()}, and an event is produced with the given inputs,
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
	public NextStatus hasNextHard();

}
