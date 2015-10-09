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

public class EmlBoolean extends EmlConstant
{
	protected final Boolean m_value;
	
	public static final EmlBoolean s_true = new EmlBoolean(true);
	
	public static final EmlBoolean s_false = new EmlBoolean(false);
	
	public EmlBoolean()
	{
		this(false);
	}
	
	protected EmlBoolean(Boolean b)
	{
		super();
		m_value = b;
	}

	public Boolean booleanValue()
	{
		return m_value;
	}
	
	public boolean boolValue()
	{
		return m_value;
	}
	
	public static void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		stack.push(EmlBoolean.toEmlBoolean(o));
	}
	
	@Override
	public String toString()
	{
		return m_value.toString();
	}
	
	@Override
	public int hashCode()
	{
		return m_value.hashCode();
	}
	
	@Override
	public boolean equals(Object o)
	{
		if (o == null || !(o instanceof EmlBoolean))
		{
			return false;
		}
		return equals((EmlBoolean) o);
	}
	
	protected boolean equals(EmlBoolean b)
	{
		return m_value.booleanValue() == b.m_value.booleanValue();
	}
	
	public static EmlBoolean toEmlBoolean(Object o)
	{
		if (o instanceof Boolean)
		{
			if ((Boolean) o)
			{
				return s_true;
			}
			{
				return s_false;
			}
		}
		if (o instanceof EmlBoolean)
		{
			return (EmlBoolean) o;
		}
		if (o instanceof String)
		{
			String s = (String) o;
			if (s.compareToIgnoreCase("true") == 0 
					|| s.compareToIgnoreCase("T") == 0
					|| s.compareToIgnoreCase("1") == 0)
			{
				return EmlBoolean.toEmlBoolean(true);
			}
			return EmlBoolean.toEmlBoolean(false);
		}
		if (o instanceof Number)
		{
			Number n = (Number) o;
			if (Math.abs(n.doubleValue()) < 0.00001)
			{
				return EmlBoolean.toEmlBoolean(false);
			}
			return EmlBoolean.toEmlBoolean(true);
		}			
		// When in doubt, return null
		return null;
	}
	
	public static boolean parseBoolValue(Object o)
	{
		if (o instanceof Boolean)
		{
			return (Boolean) o;
		}
		if (o instanceof EmlBoolean)
		{
			return ((EmlBoolean) o).boolValue();
		}
		if (o instanceof String)
		{
			String s = (String) o;
			if (s.compareToIgnoreCase("true") == 0 
					|| s.compareToIgnoreCase("T") == 0
					|| s.compareToIgnoreCase("1") == 0)
			{
				return true;
			}
			return false;
		}
		if (o instanceof Number)
		{
			Number n = (Number) o;
			if (Math.abs(n.doubleValue()) < 0.00001)
			{
				return false;
			}
			return true;
		}			
		// When in doubt, return false
		return false;
	}
}
