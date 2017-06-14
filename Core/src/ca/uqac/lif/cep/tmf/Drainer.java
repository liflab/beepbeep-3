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
package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;

/**
 * Drains an unary output processor of all its events, and returns
 * the last event produced.
 * <p>
 * Beware if the processor given for input produces an infinite stream
 * of events; if so, the {@link #drain()} method will never exit.
 * @author Sylvain Hallé
 *
 * @param <T> The type of the event to be obtained
 */
public class Drainer<T>
{
	protected Processor m_processor;
	
	/**
	 * Creates a new drainer
	 * @param p The processor to drain
	 */
	public Drainer(Processor p)
	{
		super();
		m_processor = p;
	}

	/**
	 * Drains the processor of all its outputs, and returns the last.
	 * @return The last output, or {@code null} if the processor did not
	 * produce any output
	 */
	@SuppressWarnings("unchecked")
	public T drain()
	{
		return (T) drain(m_processor);
	}
	
	/**
	 * Drains a processor of all its outputs, and returns the last.
	 * @param proc The processor to drain
	 * @return The last output, or {@code null} if the processor did not
	 * produce any output
	 */
	public static Object drain(Processor proc)
	{
		Pullable p = proc.getPullableOutput();
		Object o = null;
		while (p.hasNext())
		{
			o = p.pull();
		}
		return o;
	}

}
