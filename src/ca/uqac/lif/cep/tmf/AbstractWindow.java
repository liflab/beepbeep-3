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

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SynchronousProcessor;
import java.util.LinkedList;

/**
 * Simulates the application of a "sliding window" to a trace. It is represented
 * graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/tmf/Window.png" alt="Processor">
 * <ul>
 * <li>The processor takes as arguments another processor &phi; and a window width
 * <i>n</i></li>
 * <li>It returns the result of &phi; after processing events 0 to
 * <i>n</i>-1...</li>
 * <li>Then the result of (a new instance of &phi;) that processes
 * events 1 to <i>n</i>-1... - ...and so on</li>
 * </ul>
 * 
 * @author Sylvain Hallé
 * @since 0.8
 */
public abstract class AbstractWindow extends SynchronousProcessor
{
  /**
   * The event windows
   */
  // Initialized by reset(), used by compute().
  protected LinkedList<Object>[] m_window;

  /**
   * The window's width
   */
  protected int m_width;

  /**
   * The internal processor
   */
  protected Processor m_processor;

  /**
   * Creates a new abstract window processor
   * @param in_processor The processor to run on each window
   * @param width The width of the window
   */
  public AbstractWindow(Processor in_processor, int width)
  {
    super(in_processor.getInputArity(), in_processor.getOutputArity());
    m_width = width;
    m_processor = in_processor;
  }
}
