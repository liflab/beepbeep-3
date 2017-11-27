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

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.tmf.QueueSink;

/**
 * Unit tests for the {@link PullConstant} class.
 */
public class TestPullConstant 
{
	@Test
	public void testPullConstant1() throws ConnectorException
	{
		PullConstant pc = new PullConstant(42);
		QueueSink qs = new QueueSink();
		Connector.connect(pc, qs);
		Queue<Object> queue = qs.getQueue();
		Pushable p = pc.getPushableInput();
		p.push(0);
		Object o = queue.poll();
		assertEquals(42, ((Integer) o).intValue());
	}
	
	@Test
	public void testPullConstant2() throws ConnectorException
	{
		PullConstant pc_o = new PullConstant(42);
		PullConstant pc = pc_o.duplicate();
		QueueSink qs = new QueueSink();
		Connector.connect(pc, qs);
		Queue<Object> queue = qs.getQueue();
		Pushable p = pc.getPushableInput();
		p.push(0);
		Object o = queue.poll();
		assertEquals(42, ((Integer) o).intValue());
	}
}
