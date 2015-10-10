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

public abstract class EmlConstant extends Tuple
{
	/**
	 * Attempts to create a constant based on the contents of a string.
	 * That is, if the string contains only digits, it will create an
	 * {@link EmlNumber} instead of an {@link EmlString}.
	 * @param s The string to read from
	 * @return The constant
	 */
	public static Object createConstantFromString(String s)
	{
		int n = 0;
		try
		{
			n = Integer.parseInt(s);
		}
		catch (NumberFormatException nfe)
		{
			// This is a string
			return s;
		}
		return (Integer) n;
	}
}
