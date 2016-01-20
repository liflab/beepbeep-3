/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

/**
 * Converts a sequence of <i>n</i> consecutive events into <i>n</i>
 * events sent simultaneously to a processor as its inputs. This effectively
 * works as like time demultiplexer.
 * 
 * @author Sylvain Hallé
 *
 */
public abstract class Demultiplexer extends SingleProcessor
{
	protected List<Object> m_window;
	
	/**
	 * The width of the demuxing, i.e. the value of <i>n</i> in the
	 * definition above
	 */
	protected final int m_width;
	
	/**
	 * Creates a new demuxer
	 * @param width The width of the window
	 */
	public Demultiplexer(int width)
	{
		super(1, 1);
		m_width = width;
		m_window = new LinkedList<Object>();
	}

	@Override
	protected final Queue<Object[]> compute(Object[] inputs)
	{
		if (m_window.size() == m_width)
		{
			m_window.remove(0);
		}
		m_window.add(inputs[0]);
		if (m_window.size() == m_width)
		{
			return computeWindow(m_window.toArray());
		}
		return null;
	}
	
	protected abstract Queue<Object[]> computeWindow(Object[] window);

}
