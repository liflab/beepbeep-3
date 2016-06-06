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

import static org.junit.Assert.*;

import java.util.Queue;
import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.epl.QueueSink;

/**
 * Unit tests for the {@link Demultiplexer} class.
 * @author Sylvain Hallé
 *
 */
public class DemultiplexerTest
{
	@SuppressWarnings("unchecked")
	@Test
	public void testDemultiplexer()
	{
		Demultiplexer demux = new Demultiplexer(3);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(demux, qsink);
		Pushable push1 = demux.getPushableInput(0);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qsink.getQueue(0);
			push1.push(0);
			assertEquals(0, queue.size());
			push1.push(1);
			assertEquals(0, queue.size());
			push1.push(2);
			assertEquals(1, queue.size());
			Vector<Object> out = (Vector<Object>) queue.remove();
			assertEquals(3, out.size());
			push1.push(3);
			out = (Vector<Object>) queue.remove();
			assertEquals(3, out.size());
			push1.push(4);
			out = (Vector<Object>) queue.remove();
			assertEquals(3, out.size());
			demux.reset();
			qsink.reset();
		}
	}
}
