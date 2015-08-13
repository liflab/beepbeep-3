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
	protected Boolean m_value;
	
	public EmlBoolean()
	{
		super();
	}
	
	public EmlBoolean(Boolean b)
	{
		this();
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
	
	@Override
	public void build(Stack<Object> stack)
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
		if (o instanceof String)
		{
			String s = (String) o;
			if (s.compareToIgnoreCase("true") == 0 
					|| s.compareToIgnoreCase("T") == 0
					|| s.compareToIgnoreCase("1") == 0)
			{
				return new EmlBoolean(true);
			}
			return new EmlBoolean(false);
		}
		if (o instanceof Number)
		{
			Number n = (Number) o;
			if (Math.abs(n.doubleValue()) < 0.00001)
			{
				return new EmlBoolean(false);
			}
			return new EmlBoolean(true);
		}
		if (o instanceof Boolean)
		{
			return new EmlBoolean((Boolean) o);
		}
		if (o instanceof EmlBoolean)
		{
			return (EmlBoolean) o;
		}
			
		// When in doubt, return null
		return null;
	}

}
