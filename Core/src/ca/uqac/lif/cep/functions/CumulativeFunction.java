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
package ca.uqac.lif.cep.functions;

/**
 * A function with memory.
 */
public class CumulativeFunction<T> extends UnaryFunction<T,T>
{
	/**
	 * The last value returned by the function
	 */
	private T m_lastValue;

	/**
	 * The stateless binary function to apply on each call
	 */
	private BinaryFunction<T,T,T> m_function;

	/**
	 * Instantiates a new cumulative function
	 */
	public CumulativeFunction(BinaryFunction<T,T,T> function)
	{
		super(function.getInputTypeLeft(), function.getOutputType());
		m_function = function;
		m_lastValue = m_function.getStartValue();
	}

	@Override
	public T getValue(T x)
	{
		if (m_lastValue == null)
		{
			// If the function did not provide a start value, use the
			// first given argument as the start value
			m_lastValue = x;
			return x;
		}
		T value = m_function.getValue(m_lastValue, x);
		m_lastValue = value;
		return value;
	}
	
	@Override
	public void reset()
	{
		m_lastValue = m_function.getStartValue();
	}

	@Override
	public CumulativeFunction<T> duplicate()
	{
		return new CumulativeFunction<T>(m_function.duplicate());
	}
}
