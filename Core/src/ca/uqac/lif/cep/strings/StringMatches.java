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
package ca.uqac.lif.cep.strings;

import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * Function that checks if a string matches a regular expression
 */
public class StringMatches extends BinaryFunction<String,String,Boolean>
{
	public static final StringMatches instance = new StringMatches();
	
	StringMatches()
	{
		super(String.class, String.class, Boolean.class);
	}

	@Override
	public Boolean getValue(String s1, String s2)
	{
		return s1.matches(s2);
	}
}