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
package ca.uqac.lif.cep.signal;

import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.eml.tuples.EmlNumber;

/**
 * Finds a plateau in a data stream. A plateau is found when all
 * values in a window lie in an interval of a predetermined width.
 * By default, the interval is of width 5 and the window is of width 5.
 * <p>
 * The plateau finder does not create a new event for the same plateau
 * that continues, i.e., a new plateau will only be looked for once
 * a value lies outside the current interval. For example, in the following
 * sequence:
 * <table>
 * <tr><th>Event #</th><td>1</td><td>2</td><td>3</td><td>4</td><td>5</td><td>6</td><td>7</td><td>8</td></tr>
 * <tr><th>Value</th><td>1</td><td>2</td><td>3</td><td>2</td><td>1</td><td>2</td><td>10</td><td>8</td></tr> 
 * </table>
 * An output event will be emitted after reading event #5 (there are five
 * consecutive values all within an interval of 5), but no event will be
 * produced after reading event #6 (as it is the continuation of the current
 * plateau).
 */
public class PlateauFinder extends SingleProcessor
{
	/**
	 * The precision used to for the equality between double precision
	 * numbers
	 */
	protected static final double s_precision = 0.00001;
	
	/**
	 * The window of values to remember
	 */
	protected Vector<Double> m_values;
	
	/**
	 * The maximum value encountered so far
	 */
	protected double m_maxValue;
	
	/**
	 * The minimum value encountered so far
	 */
	protected double m_minValue;
	
	/**
	 * The range all values should lie in
	 */
	protected double m_range;

	/**
	 * Whether an output event has been sent for the current plateau
	 */
	protected boolean m_plateauFound;
	
	/**
	 * The width of the window to process
	 */
	protected int m_windowWidth;
	
	public PlateauFinder()
	{
		super(1, 1);
		m_windowWidth = 5;
		m_values = new Vector<Double>();
		m_maxValue = 0;
		m_minValue = 0;
		m_range = 5;
		m_plateauFound = false;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_values = new Vector<Double>(m_windowWidth);
		m_maxValue = 0;
		m_minValue = 0;
		m_plateauFound = false;
	}
	
	public void setWindowWidth(int width)
	{
		m_windowWidth = width;
	}
	
	public void setPlateauRange(int range)
	{
		m_range = range;
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		EmlNumber n = (EmlNumber) inputs.firstElement();
		double d = n.numberValue().doubleValue();
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
			// Window not filled yet: don't return anything
			return null;
		}
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
		// Check range of values
		double width = m_maxValue - m_minValue;
		if (width < m_range && !m_plateauFound)
		{
			// All values in the interval: create event with midpoint
			Vector<Object> out_vector = new Vector<Object>();
			out_vector.add(new EmlNumber(m_minValue + width / 2));
			// Reset everything
			m_values.clear();
			m_maxValue = 0;
			m_minValue = 0;
			return wrapVector(out_vector);
		}
		else
		{
			// No plateau found
			m_plateauFound = false;
		}
		return null;
	}
	
	protected double getMaxValue()
	{
		double value = 0;
		int pos = 0;
		for (double d : m_values)
		{
			if (pos == 0)
			{
				value = d;
			}
			else
			{
				value = Math.max(value, d);
			}
			pos++;
		}
		return value;
	}
	
	protected double getMinValue()
	{
		double value = 0;
		int pos = 0;
		for (double d : m_values)
		{
			if (pos == 0)
			{
				value = d;
			}
			else
			{
				value = Math.min(value, d);
			}
			pos++;
		}
		return value;
	}
	
	protected static boolean doubleEquals(double d1, double d2)
	{
		return Math.abs(d1 - d2) < s_precision;
	}

	@Override
	public void build(Stack<Object> stack) 
	{
		stack.pop(); // )
		Processor p = (Processor) stack.pop();
		stack.pop(); // (
		stack.pop(); // OF
		stack.pop(); // PEAK
		stack.pop(); // THE
		Connector.connect(p, this);
	}
}
