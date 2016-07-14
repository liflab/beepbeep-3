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
package ca.uqac.lif.cep.signal;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.tuples.EmlNumber;

/**
 * Finds a plateau in a data stream. A plateau is found when all
 * values in a window lie in an interval of a predetermined width.
 * By default, the interval is of width 5 and the window is of width 5.
 * <p>
 * The plateau finder outputs a non-zero event only for the first event
 * of the plateau (this has to be delayed by the width of the window).
 * It outputs zero for all other events of the plateau. Moreover,
 * new plateau will only be looked for only once
 * a value lies outside the current interval. For example, in the following
 * sequence:
 * <table summary="">
 * <tr><th>Event #</th><td>1</td><td>2</td><td>3</td><td>4</td><td>5</td><td>6</td><td>7</td><td>8</td></tr>
 * <tr><th>Value</th><td>1</td><td>2</td><td>3</td><td>2</td><td>1</td><td>2</td><td>10</td><td>8</td></tr> 
 * </table>
 * An output event will be emitted after reading event #5 (there are five
 * consecutive values all within an interval of 5), indicating that event 1
 * is the start of a plateau, but a zero event will be
 * produced for all other events, as they are the continuation of the current
 * plateau.
 */
public class PlateauFinder extends WindowProcessor
{	
	/**
	 * The range all values should lie in
	 */
	protected float m_range;

	/**
	 * Whether an output event has been sent for the current plateau
	 */
	protected boolean m_plateauFound;
	
	/**
	 * Whether the height of the plateau should be relative to that of the
	 * last plateau (<code>true</code>), or absolute (<code>false</code>)
	 */
	protected boolean m_relative;
	
	/**
	 * The value of the last plateau found. Remembering this value is
	 * necessary if the finder is set to "relative" mode 
	 * @see #setRelative(boolean)
	 */
	protected double m_lastPlateauFound;
	
	/**
	 * Instantiates a plateau finder with default settings
	 */
	public PlateauFinder()
	{
		super();
		m_range = 5;
		m_plateauFound = false;
		m_lastPlateauFound = 0;
	}
	
	/**
	 * Sets whether the height of the plateau should be relative to that of the
	 * last plateau (<code>true</code>), or absolute (<code>false</code>)
	 * @param relative See above
	 * @return A reference to the current plateau finder
	 */
	public PlateauFinder setRelative(boolean relative)
	{
		m_relative = relative;
		return this;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_plateauFound = false;
	}	
	
	/**
	 * Sets the range all values should lie in to be considered in the
	 * same plateau
	 * @param range The range
	 * @return A reference to the current plateau finder
	 */
	public PlateauFinder setPlateauRange(int range)
	{
		m_range = range;
		return this;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object[] out_vector = new Object[1];
		float d = EmlNumber.parseFloat(inputs[0]);
		if (m_values.size() < m_windowWidth)
		{
			m_values.addElement(d);
			if (m_values.size() == 1)
			{
				m_maxValue = d;
				m_minValue = d;
			}
			else
			{
				if (d > m_maxValue)
				{
					m_maxValue = d;
				}
				if (d < m_minValue)
				{
					m_minValue = d;
				}
			}
			if (m_values.size() < m_windowWidth)
			{
				// Window not filled yet: don't return anything
				return null;
			}
		}
		else
		{
			// Window is full
			// Remove first element and put new at the end
			double first_value = m_values.remove(0);
			m_values.addElement(d);
			if (doubleEquals(first_value, m_minValue))
			{
				// The element we removed was the minimum value; recompute min
				m_minValue = getMinValue();
			}
			if (doubleEquals(first_value, m_maxValue))
			{
				// The element we removed was the maximum value; recompute max
				m_maxValue = getMaxValue();
			}			
		}
		// Check range of values
		double width = m_maxValue - m_minValue;
		if (width < m_range)
		{
			if (!m_plateauFound)
			{
				// All values in the interval: create event with midpoint
				out_vector[0] = m_minValue + width / 2;
				m_plateauFound = true;				
			}
			else
			{
				out_vector[0] = 0;
			}
		}
		else
		{
			// No plateau found: emit 0
			m_plateauFound = false;
			out_vector[0] = 0;
			// Reset everything
			//m_values.clear();
			//m_maxValue = 0;
			//m_minValue = 0;
		}
		if (m_relative && ((Number) out_vector[0]).doubleValue() != 0)
		{
			Number cur_abs = (Number) out_vector[0];
			out_vector[0] = cur_abs.doubleValue() - m_lastPlateauFound;
			m_lastPlateauFound = cur_abs.doubleValue();
		}
		return wrapVector(out_vector);
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException 
	{
		stack.pop(); // )
		Processor p = (Processor) stack.pop();
		stack.pop(); // (
		stack.pop(); // OF
		stack.pop(); // PLATEAU
		stack.pop(); // THE
		PlateauFinder pf = new PlateauFinder();
		Connector.connect(p, pf);
	}

	@Override
	public PlateauFinder clone()
	{
		PlateauFinder out = new PlateauFinder();
		out.m_relative = m_relative;
		out.m_range = m_range;
		return out;
	}
}
