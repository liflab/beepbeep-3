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

import java.util.Vector;

import ca.uqac.lif.cep.SingleProcessor;

public abstract class WindowProcessor extends SingleProcessor
{
	/**
	 * The precision used to for the equality between double precision
	 * numbers
	 */
	protected static final double s_precision = 0.00001;
	
	/**
	 * The window of values to remember
	 */
	protected Vector<Float> m_values;
	
	/**
	 * The width of the window to process
	 */
	protected final int m_windowWidth;
	
	/**
	 * The maximum value encountered so far
	 */
	protected float m_maxValue;
	
	/**
	 * The minimum value encountered so far
	 */
	protected float m_minValue;

	
	public WindowProcessor()
	{
		this(5);
	}
	
	public WindowProcessor(int width)
	{
		super(1, 1);
		m_values = new Vector<Float>();
		m_windowWidth = width;
		m_maxValue = 0;
		m_minValue = 0;		
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_values = new Vector<Float>(m_windowWidth);
		m_maxValue = 0;
		m_minValue = 0;
	}
	
	protected float getMaxValue()
	{
		float value = 0;
		int pos = 0;
		for (float d : m_values)
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
	
	protected float getMinValue()
	{
		float value = 0;
		int pos = 0;
		for (float d : m_values)
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

}
