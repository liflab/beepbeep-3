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
package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import org.junit.Test;

/**
 * Unit tests for the {@link Context} object.
 */
public class TestContext 
{
	@Test
	public void testPutAll1()
	{
		Context c1 = new Context();
		c1.put("a", 0);
		c1.put("b", 1);
		Context c2 = new Context(c1);
		assertEquals(0, c2.get("a"));
		assertEquals(1, c2.get("b"));
	}
	
	@Test
	public void testPutAll2()
	{
		Context c2 = new Context(null);
		assertTrue(c2.isEmpty());
	}

}
