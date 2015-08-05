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

public class EmlString extends EmlConstant
{
	protected String m_string;
	
	public EmlString()
	{
		super();
	}
	
	public EmlString(String s)
	{
		this();
		m_string = s;
	}

	public String stringValue()
	{
		return m_string;
	}

	@Override
	public void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		if (o instanceof String)
		{
			stack.push(new EmlString((String) o));
		}
		else if (o instanceof Number)
		{
			stack.push(new EmlString(o.toString()));
		}
		
	}
	
	@Override
	public String toString()
	{
		return m_string.toString();
	}
	
	@Override
	public int hashCode()
	{
		return m_string.hashCode();
	}
	
	@Override
	public boolean equals(Object o)
	{
		if (o == null || !(o instanceof EmlString))
		{
			return false;
		}
		return equals((EmlString) o);
	}
	
	protected boolean equals(EmlString s)
	{
		return m_string.compareTo(s.m_string) == 0;
	}

}
