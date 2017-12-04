/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hall�

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
package ca.uqac.lif.cep.util;

import static org.junit.Assert.*;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.util.Lists.Pack;
import ca.uqac.lif.cep.util.Lists.Unpack;

public class PackerTest 
{
	@SuppressWarnings("unchecked")
	@Test
	public void listPackerTest1() throws ProcessorException, InterruptedException
	{
		Pack lpp = new Pack(1000);
		QueueSink sink = new QueueSink();
		Connector.connect(lpp, sink);
		Queue<Object> q = sink.getQueue();
		Pushable p = lpp.getPushableInput();
		lpp.start();
		for (int i = 0; i < 5; i++)
		{
			p.push(i);
		}
		Thread.sleep(1200);
		assertFalse(q.isEmpty());
		List<Object> list = (List<Object>) q.remove();
		assertEquals(5, list.size());
		for (int i = 20; i < 26; i++)
		{
			p.push(i);
		}
		assertTrue(q.isEmpty()); // Too early
		Thread.sleep(1200);
		list = (List<Object>) q.remove();
		assertEquals(6, list.size());
		lpp.stop();
	}
	
	@Test
	public void unpackerTest() 
	{
		Unpack lup = new Unpack();
		QueueSink sink = new QueueSink();
		Connector.connect(lup, sink);
		Queue<Object> q = sink.getQueue();
		Pushable p = lup.getPushableInput();
		List<Object> list = new LinkedList<Object>();
		for (int i = 0; i < 10; i++)
		{
			list.add(i);
		}
		p.push(list);
		assertFalse(q.isEmpty());
		assertEquals(10, q.size());
	}
}
