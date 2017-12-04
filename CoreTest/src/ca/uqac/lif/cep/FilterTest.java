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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import org.junit.Test;

import ca.uqac.lif.cep.functions.ApplyFunction;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.cep.tmf.Filter;
import ca.uqac.lif.cep.tmf.Fork;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the {@link Filter} processor
 */
public class FilterTest
{
	@Test
	public void testFilter1() 
	{
		QueueSource input1 = new QueueSource();
		input1.setEvents(new Object[]{1, 2, 3, 4});
		QueueSource input2 = new QueueSource();
		input2.setEvents(new Object[]{true, false, true, false});
		Filter f = new Filter();
		Connector.connect(input1, 0, f, 0);
		Connector.connect(input2, 0, f, 1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(f, sink);
		Number recv;
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // 1
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1, got " + recv);
		}
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}
		input1.push();
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // 1
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3, got " + recv);
		}
		input1.push();
		input2.push();
		recv = (Number) sink.remove()[0]; // null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}	
	}
	
	@Test
	public void testFilter2() 
	{
		QueueSource input1 = new QueueSource();
		input1.setEvents(new Object[]{2, 3, 4, 6});
		Fork fork = new Fork(2);
		Connector.connect(input1, fork);
		Filter filter = new Filter();
		Connector.connect(fork, 0, filter, 0);
		ApplyFunction even = new ApplyFunction(Numbers.isEven);
		Connector.connect(fork, 1, even, 0);
		Connector.connect(even, 0, filter, 1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(filter, sink);
		Number recv;
		input1.push();
		recv = (Number) sink.remove()[0]; // 2
		assertEquals(2, recv);
		input1.push();
		recv = (Number) sink.remove()[0]; // null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}
		input1.push();
		input1.push();
		recv = (Number) sink.remove()[0]; // 4
		if (recv == null || recv.intValue() != 4)
		{
			fail("Expected 4, got " + recv);
		}
		recv = (Number) sink.remove()[0]; // 6
		if (recv == null || recv.intValue() != 6)
		{
			fail("Expected 6, got " + recv);
		}
	}

}
