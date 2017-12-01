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

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;

/**
 * Unit tests for the {@link Dropper} processor.
 */
public class DropperTest
{
	@Test
	public void testDropper1()
	{
		QueueSource qs = new QueueSource().setEvents(new Object[]{new Object[]{1, 2, 3, 4}});
		Dropper d = new Dropper();
		Connector.connect(qs, d);
		Pullable p = d.getPullableOutput();
		assertEquals(1, ((Integer) p.pull()).intValue());
		assertEquals(2, ((Integer) p.pull()).intValue());
		assertEquals(3, ((Integer) p.pull()).intValue());
		assertEquals(4, ((Integer) p.pull()).intValue());
		Dropper d2 = d.duplicate();
		qs = new QueueSource().setEvents(new Object[]{new Object[]{1, 2, 3, 4}});
		Connector.connect(qs, d2);
		p = d2.getPullableOutput();
		assertEquals(1, ((Integer) p.pull()).intValue());
		assertEquals(2, ((Integer) p.pull()).intValue());
		
	}
	
	@Test
	public void testDropper2()
	{
		List<Integer> list = new ArrayList<Integer>(4);
		list.add(1);
		list.add(2);
		list.add(3);
		list.add(4);
		QueueSource qs = new QueueSource().setEvents(list);
		Dropper d = new Dropper();
		Connector.connect(qs, d);
		Pullable p = d.getPullableOutput();
		assertEquals(1, ((Integer) p.pull()).intValue());
		assertEquals(2, ((Integer) p.pull()).intValue());
		assertEquals(3, ((Integer) p.pull()).intValue());
		assertEquals(4, ((Integer) p.pull()).intValue());
	}
}
