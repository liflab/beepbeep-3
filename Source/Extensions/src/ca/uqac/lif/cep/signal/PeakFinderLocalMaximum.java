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

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.tuples.EmlNumber;

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
 * For each input event, the processor outputs the height of the peak, or
 * the value 0 if this event is not a peak. Since an event needs to be out of
 * the window to determine that it is a peak, the emission of output events
 * is delayed with respect to the consumption of input events.
 * <p>
 * By default, the window is of width 5. 
 */
public class PeakFinderLocalMaximum extends WindowProcessor
{	
	/**
	 * The position in the window where the highest value is
	 */
	protected int m_peakPosition;
	
	/**
	 * The number of events that went out of the window since the last
	 * peak was seen.
	 */
	protected int m_numSincePeak;
	
	public PeakFinderLocalMaximum()
	{
		this(5);
	}
	
	public PeakFinderLocalMaximum(int width)
	{
		super(width);
		m_peakPosition = -1;
		m_numSincePeak = 0;		
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_peakPosition = -1;
		m_numSincePeak = 0;
	}
	
	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();
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
		m_numSincePeak++;
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
				// The peak has moved out of the window.
				// First, say that all events prior to this one were not peaks
				for (int i = 0; i < m_numSincePeak - 1; i++)
				{
					Object[] out_vector = new Object[1];
					out_vector[0] = 0;
					out_queue.add(out_vector);
				}
				// Then, create output event with peak height (max - min)
				float peak_height = m_maxValue - m_minValue;
				Object[] out_vector = new Object[1];
				out_vector[0] = peak_height;
				out_queue.add(out_vector);
				// Reset everything
				m_maxValue = getMaxValue();
				m_minValue = getMinValue();
				m_peakPosition = getPeakPosition();
				m_numSincePeak = 0;
				return out_queue;
			}
		}
		return null;
	}
	
	public int getPeakPosition()
	{
		double value = 0;
		int cur_pos = 0, peak_pos = 0;
		for (double d : m_values)
		{
			if (cur_pos == 0)
			{
				value = d;
			}
			if (d > value)
			{
				value = d;
				peak_pos = cur_pos;
			}
			cur_pos++;
		}
		return peak_pos;
	}

	public static void build(Stack<Object> stack) throws ConnectorException 
	{
		stack.pop(); // )
		Processor p = (Processor) stack.pop();
		stack.pop(); // (
		stack.pop(); // OF
		stack.pop(); // PEAK
		stack.pop(); // THE
		PeakFinderLocalMaximum pflm = new PeakFinderLocalMaximum();
		Connector.connect(p, pflm);
	}
	
	@Override
	public PeakFinderLocalMaximum clone()
	{
		return new PeakFinderLocalMaximum(m_windowWidth);
	}

}
