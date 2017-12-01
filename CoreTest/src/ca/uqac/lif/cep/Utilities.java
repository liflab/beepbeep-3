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
package ca.uqac.lif.cep;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.Queue;

import org.junit.Test;

public class Utilities 
{
	@Test
	public void dummyTest()
	{
		// Dummy test, just so JUnit won't complain about a class
		// that has no test in it
	}
	
	public static void queueContains(int value, Queue<Object> queue)
	{
		assertEquals(1, queue.size());
		Object o = queue.remove();
		assertNotNull(o);
		assertTrue(o instanceof Number);
		assertEquals(value, ((Number) o).intValue());
	}
	
	public static void assertEquals(int i, Object o)
	{
		assertTrue(o instanceof Number);
		org.junit.Assert.assertEquals(i, ((Number) o).intValue());
	}
	
	/**
	 * Converts a string into an input stream
	 * @param s The string to read from
	 * @return The input stream with the contents of the string
	 */
	public static InputStream toInputStream(String s)
	{
		return new ByteArrayInputStream(s.getBytes());
	}
}
