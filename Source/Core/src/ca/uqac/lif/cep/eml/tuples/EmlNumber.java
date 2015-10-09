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
package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

import ca.uqac.lif.cep.Processor;

public class EmlNumber extends EmlConstant
{
	protected final float m_number;
	
	public EmlNumber()
	{
		this(0);
	}
	
	public EmlNumber(float n)
	{
		super();
		m_number = n;
	}
	
	public EmlNumber(Number n)
	{
		this(n.floatValue());
	}
	
	public EmlNumber(EmlNumber n)
	{
		this(n.m_number);
	}
	
	public int intValue()
	{
		return (int) m_number;
	}
	
	public float floatValue()
	{
		return m_number;
	}
	
	public double doubleValue()
	{
		return m_number;
	}

	public static void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		if (o instanceof Processor)
		{
			stack.push(o);
		}
		else
		{
			stack.push(EmlNumber.toEmlNumber(o));
		}
	}
	
	@Override
	public String toString()
	{
		if (m_number % 1 == 0)
		{
			// Display as integer
			return Integer.toString((int) m_number);
		}
		return Float.toString(m_number);
	}
	
	@Override
	public int hashCode()
	{
		return (int) m_number;
	}
	
	@Override
	public boolean equals(Object o)
	{
		if (o == null || !(o instanceof EmlNumber))
		{
			return false;
		}
		return equals((EmlNumber) o);
	}
	
	protected boolean equals(EmlNumber n)
	{
		return m_number == n.m_number;
	}
	
	/**
	 * Attempts to create an EmlNumber from the object passed as an argument
	 * @param o The object
	 * @return An EmlNumber, or null if no number could be build from
	 *   the argument
	 */
	public static EmlNumber toEmlNumber(Object o)
	{
		if (o instanceof EmlNumber)
		{
			return new EmlNumber((EmlNumber) o);
		}
		if (o instanceof Number)
		{
			return new EmlNumber((Number) o);
		}
		if (o instanceof String)
		{
			return new EmlNumber(Double.parseDouble((String) o));
		}
		if (o instanceof NamedTuple)
		{
			NamedTuple t = (NamedTuple) o;
			if (t.size() == 1)
			{
				// If we have a tuple with a single element, try to make a
				// number with that element
				for (String s : t.keySet())
				{
					EmlConstant c = t.get(s);
					if (c != null)
					{
						return EmlNumber.toEmlNumber(c);
					}
				}
			}
		}
		return null;
	}
	
	/**
	 * Attempts to create a float from the object passed as an argument
	 * @param o The object
	 * @return The float, or 0 if no float could be produced from the argument
	 */
	public static float parseFloat(Object o)
	{
		if (o instanceof EmlNumber)
		{
			return ((EmlNumber) o).m_number;
		}
		if (o instanceof Number)
		{
			return ((Number) o).floatValue();
		}
		if (o instanceof String)
		{
			return Float.parseFloat((String) o);
		}
		if (o instanceof EmlString)
		{
			return Float.parseFloat(o.toString());
		}
		if (o instanceof NamedTuple)
		{
			NamedTuple t = (NamedTuple) o;
			if (t.size() == 1)
			{
				// If we have a tuple with a single element, try to make a
				// number with that element
				for (String s : t.keySet())
				{
					EmlConstant c = t.get(s);
					if (c != null)
					{
						return EmlNumber.parseFloat(c);
					}
				}
			}
		}
		return 0;
	}
}
