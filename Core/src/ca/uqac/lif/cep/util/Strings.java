/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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
package ca.uqac.lif.cep.util;

import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * A container object for string functions
 * @author Sylvain Hallé
 */
public class Strings 
{
	private Strings()
	{
		// Utility class
	}
	
	/**
	 * Concatenates two strings
	 */
	public static class Concat extends BinaryFunction<String,String,String>
	{
		public static final Concat instance = new Concat();
		
		protected Concat()
		{
			super(String.class, String.class, String.class);
		}

		@Override
		public String getValue(String s1, String s2)
		{
			return s1 + s2;
		}
	}
	
	/**
	 * Function that checks if a string contains another
	 */
	public static class Contains extends BinaryFunction<String,String,Boolean>
	{
		public static final Contains instance = new Contains();
		
		protected Contains()
		{
			super(String.class, String.class, Boolean.class);
		}

		@Override
		public Boolean getValue(String s1, String s2)
		{
			return s1.contains(s2);
		}
	}
	
	/**
	 * Function that checks if a string ends by another
	 */
	public static class EndsWith extends BinaryFunction<String,String,Boolean>
	{
		public static final EndsWith instance = new EndsWith();
		
		protected EndsWith()
		{
			super(String.class, String.class, Boolean.class);
		}

		@Override
		public Boolean getValue(String s1, String s2)
		{
			return s1.endsWith(s2);
		}
	}
	
	/**
	 * Checks if a string matches a regular expression
	 */
	public static class Matches extends BinaryFunction<String,String,Boolean>
	{
		public static final Matches instance = new Matches();
		
		protected Matches()
		{
			super(String.class, String.class, Boolean.class);
		}

		@Override
		public Boolean getValue(String s1, String s2)
		{
			return s1.matches(s2);
		}
	}
	
	/**
	 * Checks if a string starts by another
	 */
	public static class StartsWith extends BinaryFunction<String,String,Boolean>
	{
		public static final StartsWith instance = new StartsWith();
		
		protected StartsWith()
		{
			super(String.class, String.class, Boolean.class);
		}

		@Override
		public Boolean getValue(String s1, String s2)
		{
			return s1.startsWith(s2);
		}
	}
}
