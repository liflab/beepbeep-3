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

import ca.uqac.lif.cep.tmf.TimeDecimate;
import org.junit.Test;

import ca.uqac.lif.cep.ProcessorTest.Sum;
import ca.uqac.lif.cep.ProvenanceTest.DummyTracker;
import ca.uqac.lif.cep.tmf.CountDecimate;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for {@link CountDecimate} and {@link TimeDecimate}.
 */
public class DecimateTest
{
	@Test
	public void testDecimatePull1() 
	{
		int op_num = 0;
		QueueSource ones = new QueueSource(1);
		ones.addEvent(1);
		Sum count = new Sum();
		Connector.connect(ones, count);
		CountDecimate decim = new CountDecimate(2);
		Connector.connect(count, decim);
		QueueSink sink = new QueueSink(1);
		Connector.connect(decim, sink);
		Number recv;
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1 on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv != null)
		{
			fail("Expected null on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv != null)
		{
			fail("Expected null on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 5)
		{
			fail("Expected 5 on pull " + op_num + ", got " + recv);
		}
	}
	
	@Test
	public void testDecimatePush1() 
	{
		int op_num = 0;
		QueueSource ones = new QueueSource(1);
		ones.addEvent(1);
		Sum count = new Sum();
		Connector.connect(ones, count);
		CountDecimate decim = new CountDecimate(2);
		Connector.connect(count, decim);
		QueueSink sink = new QueueSink(1);
		Connector.connect(decim, sink);
		Number recv;
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1 on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv != null)
		{
			fail("Expected null on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv != null)
		{
			fail("Expected null on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove()[0];
		if (recv == null || recv.intValue() != 5)
		{
			fail("Expected 5 on push " + op_num + ", got " + recv);
		}
	}
	
	@Test
	public void testDecimateTracker()
	{
		QueueSource qs = new QueueSource().setEvents(0, 1, 2, 3, 4);
		CountDecimate cd = new CountDecimate(2);
		Connector.connect(qs, cd);
		DummyTracker dt = new DummyTracker();
		dt.setTo(qs, cd);
		Pullable p = cd.getPullableOutput();
		p.pull();
		assertTrue(dt.containsInputAssociation(cd.getId(), 0, 0, 0, 0));
		p.pull();
		assertTrue(dt.containsInputAssociation(cd.getId(), 0, 2, 0, 1));
	}
}
