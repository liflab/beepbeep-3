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
 * Finds a peak in a data stream using the
 * <a href="http://www.originlab.com/doc/Origin-Help/PA-Algorithm#Local_Maximum">local
 * maximum algorithm</a>.
 * <p>
 * The local maximum method is a brute force searching algorithm which finds
 * the local maximum in a moving window. The window size is determined by a 
 * predefined a number of local points.
 * <p>
 * Initially, an <i>n</i>-point window is placed at the start point of data stream. 
 * The maximum in this window, as well as its index, is recorded. Then the 
 * window is moved one step further. If the new maximun is greater than 
 * the saved maximum, update both the maximum value and index value and then 
 * move forward. If the maximum moves out of the window, i.e. all points in 
 * the window are less than the maximum, a peak is found an the whole window 
 * configuration is reconstructed for the next peak.
 * <p>
 * By default, the window is of width 5. 
 */
public class PeakFinder extends SingleProcessor
{
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
	 * The width of the window to process
	 */
	protected int m_windowWidth;
	
	/**
	 * The position in the window where the highest value is
	 */
	protected int m_peakPosition;
	
	public PeakFinder()
	{
		super(1, 1);
		m_windowWidth = 5;
		m_values = new Vector<Double>();
		m_peakPosition = -1;
		m_maxValue = 0;
		m_minValue = 0;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_values = new Vector<Double>(m_windowWidth);
		m_peakPosition = -1;
		m_maxValue = 0;
		m_minValue = 0;
	}
	
	public void setWindowWidth(int width)
	{
		m_windowWidth = width;
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
					m_peakPosition = m_values.size() - 1;
				}
				if (d < m_minValue)
				{
					m_minValue = d;
				}
			}
			// Window not filled yet: don't return anything
			return null;
		}
		// Window is full; remove first element and put new at the end
		m_values.remove(0);
		m_values.addElement(d);
		m_peakPosition--; // This moves the current peak one position to the left
		if (d > m_maxValue)
		{
			// Current value higher than current peak: update
			m_maxValue = d;
			m_peakPosition = m_windowWidth - 1;
		}
		else
		{
			if (m_peakPosition < 0)
			{
				// The peak has moved out of the window: create output event
				// with peak height (max - min)
				double peak_height = m_maxValue - m_minValue;
				Vector<Object> out_vector = new Vector<Object>();
				out_vector.add(new EmlNumber(peak_height));
				// Reset everything
				m_values.clear();
				m_maxValue = 0;
				m_minValue = 0;
				m_peakPosition = -1;
				return wrapVector(out_vector);
			}
		}
		return null;
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
