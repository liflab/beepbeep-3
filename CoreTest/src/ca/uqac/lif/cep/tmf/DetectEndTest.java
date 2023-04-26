/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2023 Sylvain Hallé

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

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.functions.Constant;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.functions.StreamVariable;
import ca.uqac.lif.cep.util.Equals;

/**
 * Unit tests for {@link DetectEnd}.
 */
public class DetectEndTest
{
	@Test
	public void test1()
	{
		DetectEnd e = new DetectEnd(new FunctionTree(Equals.instance, StreamVariable.X, new Constant(0)));
		QueueSink sink = new QueueSink();
		Connector.connect(e, sink);
		Queue<?> q = sink.getQueue();
		Pushable p = e.getPushableInput();
		p.push(1);
		assertEquals(1, q.size());
		assertEquals(1, q.remove());
		p.push(0);
		assertEquals(0, q.size());
		p.push(2);
		assertEquals(0, q.size());
	}
}
