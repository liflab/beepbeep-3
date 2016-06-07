package ca.uqac.lif.cep.signal;

import java.util.Queue;

import ca.uqac.lif.cep.tuples.EmlNumber;

/**
 * Finds peaks in a sequence of numerical values using the "travel-rise"
 * technique. This works <a href="http://stackoverflow.com/a/44357">as follows</a>:
 * <p>
 * Between any two points in your data, (x(0),y(0)) and (x(n),y(n)),
 * add up y(i+1)-y(i) for 0 &lt;= i &lt; n and call this T ("travel") and set R 
 * ("rise") to y(n)- y(0) + k for suitably small k. T/R &gt; 1 indicates a 
 * peak. This works OK if large travel due to noise is unlikely or if noise 
 * distributes symmetrically around a base curve shape. 
 * 
 * @author Sylvain
 *
 */
public class PeakFinderTravelRise extends WindowProcessor
{
	
	protected static final float s_k = 1f;
	
	public PeakFinderTravelRise(int width)
	{
		super(width);
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		m_values.addElement(EmlNumber.parseFloat(inputs[0]));
		if (m_values.size() == m_windowWidth + 1)
		{
			m_values.remove(0);
		}
		if (m_values.size() == m_windowWidth)
		{
			float T = 0;
			boolean first = true;
			float last_value = 0;
			for (float f : m_values)
			{
				if (first)
				{
					first = false;
				}
				else
				{
					T += (f - last_value);
				}
				last_value = f;
			}
			float R = m_values.lastElement() - m_values.firstElement() + s_k;
			if (T/R > 1)
			{
				System.out.print(T/R + " ");
				// Declare a peak
				return wrapObject(getMaxValue() - getMinValue());
			}
		}
		return wrapObject(0);
	}
	
	@Override
	public PeakFinderTravelRise clone()
	{
		return new PeakFinderTravelRise(m_windowWidth);
	}

}
