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

/**
 * Creates a feed of events from comma-separated string chunks.
 * Note that the input feed must have a trailing comma for all elements,
 * including the last.
 * @author sylvain
 *
 */
public class CsvFeeder extends TokenFeeder
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 5141532668453381253L;
	/**
	 * Whether to apply the {@link String#trim() trim()} method on the
	 * resulting token
	 */
	protected boolean m_trimSpaces = true;
	
	public CsvFeeder()
	{
		super();
		m_separatorBegin = "";
		m_separatorEnd = ",";
	}

	@Override
	protected Object createTokenFromInput(String token)
	{
		// Remove trailing comma
		if (m_trimSpaces)
		{
			return token.substring(0, token.length() - 1).trim();
		}
		return token.substring(0, token.length() - 1);
	}

	@Override
	public CsvFeeder duplicate()
	{
		return new CsvFeeder();
	}
}
