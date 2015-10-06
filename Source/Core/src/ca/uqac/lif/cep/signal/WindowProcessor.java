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
	protected int m_windowWidth = 1;
	
	/**
	 * The maximum value encountered so far
	 */
	protected double m_maxValue;
	
	/**
	 * The minimum value encountered so far
	 */
	protected double m_minValue;

	
	public WindowProcessor()
	{
		super(1, 1);
		m_values = new Vector<Float>();
		m_windowWidth = 5;
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

	
	public void setWindowWidth(int width)
	{
		m_windowWidth = width;
	}

	protected static boolean doubleEquals(double d1, double d2)
	{
		return Math.abs(d1 - d2) < s_precision;
	}

}
