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

import static org.junit.Assert.*;

import java.util.Map;
import java.util.Queue;
import java.util.Stack;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.CumulativeProcessor;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.Slicer;

/**
 * Unit tests for the {@link Slicer} processor.
 * @author Sylvain Hallé
 */
public class SlicerTest extends BeepBeepUnitTest
{
	@SuppressWarnings("unchecked")
	@Test
	public void testSlicer1() 
	{
		Slicer sli = new Slicer(new IsEven(), new Sum());
		QueueSink qsink = new QueueSink(1);
		Connector.connect(sli,  qsink);
		Pushable in = sli.getPushableInput(0);
		Map<Object,Object> map;
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qsink.getQueue(0);
			in.push(1);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(1.0f, map.get(false));
			in.push(1);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(2.0f, map.get(false));
			in.push(6);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(2.0f, map.get(false));
			assertEquals(6.0f, map.get(true));
			in.push(2);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(2.0f, map.get(false));
			assertEquals(8.0f, map.get(true));
			in.push(3);
			map = (Map<Object,Object>) queue.poll();
			assertEquals(5.0f, map.get(false));
			assertEquals(8.0f, map.get(true));
			sli.reset();
			qsink.reset();
		}
	}
	
	public static class Sum extends CumulativeProcessor
	{
		public Sum()
		{
			super(new CumulativeFunction<Number>(Addition.instance));
		}
	}

	public static class IsEven extends UnaryFunction<Number,Boolean>
	{
		public IsEven()
		{
			super(Number.class, Boolean.class);
		}
		
		@Override
		public Boolean getValue(Number x) 
		{
			return x.intValue() % 2 == 0;
		}
		
		public static void build(Stack<Object> stack) 
		{
			stack.pop(); // ISEVEN
			stack.push(new IsEven());
		}
	}
}
