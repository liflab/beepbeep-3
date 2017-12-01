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

import static org.junit.Assert.assertEquals;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for a few simple processors: {@link PullConstant}, 
 * {@link Passthrough}
 * @author Sylvain Hallé
 */
public class SimpleTests
{
	@Test
	public void testConstant() 
	{
		String out = null;
		QueueSource c = new QueueSource();
		c.setEvents(new Object[]{"A"});
		TypedPullable<String> p = new TypedPullable<String>(c.getPullableOutput(0));
		out = p.pullSoft();
		assertEquals("A", out);
		out = p.pullSoft();
		assertEquals("A", out);
	}
	
	@Test
	public void testPassthrough() 
	{
		Passthrough c = new Passthrough(1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(c,  sink);
		Pushable in = c.getPushableInput(0);
		Queue<Object> q = sink.getQueue(0);
		for (int i = 0; i < 10; i++)
		{
			in.push(i);
			int out = ((Number) q.remove()).intValue();
			assertEquals(i, out);
		}
	}
}
