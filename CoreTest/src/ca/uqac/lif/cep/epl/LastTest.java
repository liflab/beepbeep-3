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
package ca.uqac.lif.cep.epl;

import static org.junit.Assert.*;

import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;

public class LastTest 
{
	@Test
	public void test1() throws ConnectorException
	{
		Object o;
		QueueSource source1 = new QueueSource(null, 1);
		source1.loop(false);
		{
			Vector<Object> events = new Vector<Object>();
			events.add(0);
			events.add(1);
			events.add(2);
			source1.setEvents(events);
		}
		Last s = new Last();
		Connector.connect(source1, s);
		Pullable p = s.getPullableOutput(0);
		o = p.pullHard();
		assertNotNull(o);
		assertEquals(2, ((Integer) o).intValue());
		o = p.pullHard();
		assertNull(o);
		o = p.pullHard();
		assertNull(o);
	}
}
