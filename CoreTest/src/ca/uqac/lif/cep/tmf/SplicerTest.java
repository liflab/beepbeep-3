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
package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.*;

import org.junit.Test;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Splice;

/**
 * Unit tests for the {@link Splice} processor.
 */
public class SplicerTest 
{
	@Test
	public void test1()
	{
		Object o;
		QueueSource source1 = new QueueSource(1);
		source1.loop(false);
		source1.setEvents(0, 1, 2);
		QueueSource source2 = new QueueSource(1);
		source2.loop(false);
		source2.setEvents(3, 4, 5);
		Splice s = new Splice(source1, source2);
		Context c = new Context();
		c.put("b", 10);
		s.setContext(c);
		assertEquals(10, source1.getContext("b"));
		assertEquals(10, source2.getContext("b"));
		s.setContext("a", 3);
		assertEquals(3, source1.getContext("a"));
		assertEquals(3, source2.getContext("a"));
		Pullable p = s.getPullableOutput(0);
		o = p.pull();
		assertNotNull(o);
		assertEquals(0, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(1, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(2, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(3, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(4, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(5, ((Integer) o).intValue());
		o = p.pull();
		assertNull(o);
		o = p.pull();
		assertNull(o);
		s.reset();
		o = p.pull();
		assertNotNull(o);
		assertEquals(0, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(1, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(2, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(3, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(4, ((Integer) o).intValue());
		o = p.pull();
		assertEquals(5, ((Integer) o).intValue());
		o = p.pull();
		assertNull(o);
		o = p.pull();
		assertNull(o);
	}
}
