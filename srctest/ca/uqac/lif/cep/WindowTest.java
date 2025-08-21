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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.fail;

import org.junit.Test;

import ca.uqac.lif.cep.ProcessorTest.Sum;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Window;

/**
 * Unit tests for the {@link Window}.
 * @author Sylvain Hallé
 */
public class WindowTest 
{
	@Test
	public void testWindowPull1() 
	{
		Number recv;
		QueueSource cs = new QueueSource(1); // Sequence of 1s
		cs.addEvent(1);
		Window wp = new Window(new Sum(), 3);
		Connector.connect(cs, wp);
		Pullable p = wp.getPullableOutput(0);
		// We must pull three times to get the first output
		recv = (Number) p.pullSoft();
		assertNull(recv);
		recv = (Number) p.pullSoft();
		assertNull(recv); // 1 + 1 = 2
		recv = (Number) p.pullSoft();
		assertEquals(3, recv.intValue()); // 2 + 1 = 3
		recv = (Number) p.pullSoft();
		assertEquals(3, recv.intValue());
	}
	
	@Test
	public void testWindowPull2() 
	{
		Number recv;
		QueueSource cs = new QueueSource(1); // Sequence of 1s
		cs.addEvent(1);
		Window wp = new Window(new Sum(), 3);
		Connector.connect(cs, wp);
		Pullable p = wp.getPullableOutput(0);
		// We pull hard: get output on first call
		recv = (Number) p.pull();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on first pull, got " + recv);
		}
		recv = (Number) p.pull();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on second pull, got " + recv);
		}
	}

	
	@Test
	public void testWindowPush1() 
	{
		Number recv;
		QueueSource cs = new QueueSource(1); // Sequence of 1s
		cs.addEvent(1);
		Window wp = new Window(new Sum(), 3);
		QueueSink qs = new QueueSink(1);
		Connector.connect(cs, wp);
		Connector.connect(wp, qs);
		// We must push three times to get the first output
		cs.push();
		recv = (Number) qs.remove()[0];
		if (recv != null)
		{
			fail("Expected null on first push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove()[0];
		if (recv != null)
		{
			fail("Expected null on second push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove()[0];
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on third push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove()[0];
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on fourth push, got " + recv);
		}
	}
}
