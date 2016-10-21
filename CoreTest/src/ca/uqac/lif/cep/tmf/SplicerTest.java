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

import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Splicer;

public class SplicerTest 
{
	@Test
	public void test1()
	{
		Object o;
		QueueSource source1 = new QueueSource(1);
		source1.loop(false);
		{
			Vector<Object> events = new Vector<Object>();
			events.add(0);
			events.add(1);
			events.add(2);
			source1.setEvents(events);
		}
		QueueSource source2 = new QueueSource(1);
		source2.loop(false);
		{
			Vector<Object> events = new Vector<Object>();
			events.add(3);
			events.add(4);
			events.add(5);
			source2.setEvents(events);
		}
		Splicer s = new Splicer(source1, source2);
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
	}
}
