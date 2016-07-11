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

import static org.junit.Assert.assertTrue;

import java.util.Queue;
import java.util.Stack;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.CumulativeProcessor;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.UnaryFunction;
import ca.uqac.lif.cep.Utilities;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.numbers.NumberGrammar;

/**
 * Unit tests for the {@link Slicer} processor.
 * @author Sylvain Hallé
 */
public class SlicerTest
{
	@Test
	public void testSlicer1() throws ConnectorException
	{
		Slicer sli = new Slicer(new IsEven(), new Sum());
		QueueSink qsink = new QueueSink(1);
		Connector.connect(sli,  qsink);
		Pushable in = sli.getPushableInput(0);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qsink.getQueue(0);
			in.push(1);
			Utilities.queueContains(1, queue);
			in.push(1);
			Utilities.queueContains(2, queue);
			in.push(6);
			Utilities.queueContains(6, queue);
			in.push(2);
			Utilities.queueContains(8, queue);
			in.push(3);
			Utilities.queueContains(5, queue);
			sli.reset();
			qsink.reset();
		}
	}
	
	@Test
	public void testSlicerParse() throws ParseException, ConnectorException
	{
		Interpreter my_int = new Interpreter();
		my_int.extendGrammar(NumberGrammar.class);
		Object o = my_int.parseQuery("SLICE (1) WITH (1) ON ADDITION");
		assertTrue(o instanceof Processor);
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
		public Boolean evaluate(Number x) 
		{
			return x.intValue() % 2 == 0;
		}
		
		public static void build(Stack<Object> stack) throws ConnectorException
		{
			stack.pop(); // ISEVEN
			stack.push(new IsEven());
		}
	}
}
