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
package ca.uqac.lif.cep.input;

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Transforms a comma-separated line of text into an array
 * @author Sylvain Hallé
 */
public class SplitString extends UnaryFunction<String,Object>
{
	/**
	 * An instance of this function with default values 
	 */
	public static final transient SplitString instance = new SplitString(":");
	
	/**
	 * The symbol used to separate data fields
	 */
	protected String m_separator = ":";
	
	/**
	 * Whether to trim each part of the string before processing
	 */
	protected boolean m_trim = true;
	
	public SplitString(String separator)
	{
		super(String.class, Object.class);
		m_separator = separator;
	}
	
	/**
	 * Sets whether to apply <tt>trim()</tt> to each substring
	 * @param b Set to {@code true} to trim, {@code false} otherwise
	 * @return This function
	 */
	public SplitString trim(boolean b)
	{
		m_trim = b;
		return this;
	}

	@Override
	public Object getValue(String s) 
	{
		String[] parts = s.split(m_separator);
		Object[] typed_parts = new Object[parts.length];
		for (int i = 0; i < parts.length; i++)
		{
			if (m_trim)
			{
				typed_parts[i] = createConstantFromString(parts[i].trim());
			}
			else
			{
				typed_parts[i] = createConstantFromString(parts[i]);
			}
		}
		return typed_parts;
	}
	
	/**
	 * Attempts to create a constant based on the contents of a string.
	 * That is, if the string contains only digits, it will create an
	 * number instead of a string.
	 * @param s The string to read from
	 * @return The constant
	 */
	public static Object createConstantFromString(String s)
	{
		try
		{
			return Integer.parseInt(s); 
		}
		catch (NumberFormatException nfe1)
		{
			try
			{
				return Float.parseFloat(s);
			}
			catch (NumberFormatException nfe2)
			{
				// Do nothing
			}
		}
		// This is a string
		return s;
	}
}
