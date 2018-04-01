/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2018 Sylvain Hallé

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

import java.util.LinkedList;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * Simulates the application of a "sliding window" to a trace.
 * It is represented graphically as:
 * 
 * ![Window]({@docRoot}/doc-files/tmf/Window.png)
 * 
 * -The processor takes as arguments another processor &phi; and a
 *  window width *n*
 * - It returns the result of &phi; after processing events 0 to
 *   <i>n</i>-1...
 * - Then the result of (a new instance of &phi;) that processes
 *   events 1 to <i>n</i>-1...
 * - ...and so on
 * 
 * There are two "flavors" of Window: one that pushes events to the
 * internal processor {@link Window} and one that pull events from
 * the internal processor {@link WindowPull}.
 * @author Sylvain Hallé
 * 
 */
public abstract class AbstractWindow extends SingleProcessor
{
	/**
	 * The event windows
	 */
	protected LinkedList<Object>[] m_window;
	
	/**
	 * The window's width
	 */
	protected int m_width;

	/**
	 * The internal processor
	 */
	protected Processor m_processor = null;
	
	public AbstractWindow(Processor in_processor, int width)
	{
		super(in_processor.getInputArity(), in_processor.getOutputArity());
		m_width = width;
		m_processor = in_processor;
	}
}
