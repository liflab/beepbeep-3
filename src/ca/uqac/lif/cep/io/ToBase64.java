/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2026 Sylvain Hallé

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
package ca.uqac.lif.cep.io;

import java.util.Base64;

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Converts a byte array representing an image into a Base64-encoded
 * string.
 * @author Sylvain Hallé
 * @since 3.14
 */
public class ToBase64 extends UnaryFunction<byte[], String>
{
	/**
	 * A singleton instance of the function.
	 */
	public static final ToBase64 instance = new ToBase64();
	
	/**
	 * Creates a new instance of the function.
	 */
	protected ToBase64()
	{
		super(byte[].class, String.class);
	}

	@Override
	public String getValue(byte[] bytes)
	{
		return Base64.getEncoder().encodeToString(bytes);
	}
}
