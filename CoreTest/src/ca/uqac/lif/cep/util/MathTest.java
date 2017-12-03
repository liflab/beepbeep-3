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
package ca.uqac.lif.cep.util;

import static org.junit.Assert.*;

import java.util.Queue;
import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.ApplyFunction;
import ca.uqac.lif.cep.functions.FunctionsTest;
import ca.uqac.lif.cep.tmf.ReplaceWith;
import ca.uqac.lif.cep.tmf.Filter;
import ca.uqac.lif.cep.tmf.Fork;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Window;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.cep.util.Numbers.NumberCast;

/**
 * Unit tests for basic arithmetic functions
 * @author Sylvain Hallé
 */
public class MathTest
{
	@Test
	public void testAddition()
	{
		assertEquals(8f, FunctionsTest.evaluate(Numbers.addition, 3, 5));
		assertTrue(Numbers.addition.toString().length() >= 1);
		assertEquals(0f, Numbers.addition.getStartValue());
	}
	
	@Test
	public void testSubtraction()
	{
		assertEquals(-2f, FunctionsTest.evaluate(Numbers.subtraction, 3, 5));
		assertTrue(Numbers.subtraction.toString().length() >= 1);
		assertEquals(0f, Numbers.subtraction.getStartValue());
	}
	
	@Test
	public void testMultiplication()
	{
		assertEquals(15f, FunctionsTest.evaluate(Numbers.multiplication, 3, 5));
		assertTrue(Numbers.multiplication.toString().length() >= 1);
		assertEquals(1f, Numbers.multiplication.getStartValue());
	}
	
	@Test
	public void testDivision()
	{
		assertEquals(0.6f, FunctionsTest.evaluate(Numbers.division, 3, 5));
		assertTrue(Numbers.division.toString().length() >= 1);
		assertEquals(1f, Numbers.division.getStartValue());
	}
	
	@Test
	public void testPower()
	{
		assertEquals(81d, FunctionsTest.evaluate(Numbers.power, 3, 4));
		assertTrue(Numbers.power.toString().length() >= 1);
		assertEquals(1f, Numbers.power.getStartValue());
	}
	
	@Test
	public void testSqrt()
	{
		assertEquals(3d, FunctionsTest.evaluate(Numbers.squareRoot, 9));
		assertTrue(Numbers.squareRoot.toString().length() >= 1);
	}
	
	@Test
	public void testSignum()
	{
		assertEquals(1, FunctionsTest.evaluate(Numbers.signum, 9));
		assertEquals(0, FunctionsTest.evaluate(Numbers.signum, 0));
		assertEquals(-1, FunctionsTest.evaluate(Numbers.signum, -2));
		assertTrue(Numbers.signum.toString().length() >= 1);
	}
	
	@Test
	public void testMaximum()
	{
		assertEquals(4f, FunctionsTest.evaluate(Numbers.maximum, 3, 4));
		assertEquals(4f, FunctionsTest.evaluate(Numbers.maximum, 4, 3));
		assertTrue(Numbers.maximum.toString().length() >= 1);
		assertEquals(Float.MIN_VALUE, Numbers.maximum.getStartValue());
	}
	
	@Test
	public void testMinimum()
	{
		assertEquals(3f, FunctionsTest.evaluate(Numbers.minimum, 3, 4));
		assertEquals(3f, FunctionsTest.evaluate(Numbers.minimum, 4, 3));
		assertTrue(Numbers.minimum.toString().length() >= 1);
		assertEquals(Float.MAX_VALUE, Numbers.minimum.getStartValue());
	}
	
	@Test
	public void testGte()
	{
		assertEquals(false, FunctionsTest.evaluate(Numbers.isGreaterOrEqual, 3, 4));
		assertEquals(true, FunctionsTest.evaluate(Numbers.isGreaterOrEqual, 4, 3));
		assertEquals(true, FunctionsTest.evaluate(Numbers.isGreaterOrEqual, 3, 3));
		assertTrue(Numbers.isGreaterOrEqual.toString().length() >= 1);
		assertEquals(false, Numbers.isGreaterOrEqual.getStartValue());
	}
	
	@Test
	public void testGt()
	{
		assertEquals(false, FunctionsTest.evaluate(Numbers.isGreaterThan, 3, 4));
		assertEquals(true, FunctionsTest.evaluate(Numbers.isGreaterThan, 4, 3));
		assertEquals(false, FunctionsTest.evaluate(Numbers.isGreaterThan, 3, 3));
		assertTrue(Numbers.isGreaterThan.toString().length() >= 1);
		assertEquals(false, Numbers.isGreaterThan.getStartValue());
	}
	
	@Test
	public void testLte()
	{
		assertEquals(true, FunctionsTest.evaluate(Numbers.isLessOrEqual, 3, 4));
		assertEquals(false, FunctionsTest.evaluate(Numbers.isLessOrEqual, 4, 3));
		assertEquals(true, FunctionsTest.evaluate(Numbers.isLessOrEqual, 3, 3));
		assertTrue(Numbers.isLessOrEqual.toString().length() >= 1);
		assertEquals(false, Numbers.isLessOrEqual.getStartValue());
	}
	
	@Test
	public void testLt()
	{
		assertEquals(true, FunctionsTest.evaluate(Numbers.isLessThan, 3, 4));
		assertEquals(false, FunctionsTest.evaluate(Numbers.isLessThan, 4, 3));
		assertEquals(false, FunctionsTest.evaluate(Numbers.isLessThan, 3, 3));
		assertTrue(Numbers.isLessThan.toString().length() >= 1);
		assertEquals(false, Numbers.isLessThan.getStartValue());
	}
	
	@Test
	public void testAbsoluteValue()
	{
		assertEquals(3f, FunctionsTest.evaluate(Numbers.absoluteValue, 3));
		assertEquals(3f, FunctionsTest.evaluate(Numbers.absoluteValue, -3));
		assertEquals(0f, FunctionsTest.evaluate(Numbers.absoluteValue, 0));
		assertTrue(Numbers.absoluteValue.toString().length() >= 1);
	}
	
	@Test
	public void testIsEven()
	{
		assertEquals(true, FunctionsTest.evaluate(Numbers.isEven, 2));
		assertEquals(true, FunctionsTest.evaluate(Numbers.isEven, -2));
		assertEquals(false, FunctionsTest.evaluate(Numbers.isEven, 3));
		assertEquals(false, FunctionsTest.evaluate(Numbers.isEven, 2.4));
		assertTrue(Numbers.isEven.toString().length() >= 1);
	}
	
	@Test
	public void testNumberCast1()
	{
		Number n;
		n = (Number) FunctionsTest.evaluate(Numbers.numberCast, 2);
		assertTrue(n instanceof Integer);
		assertEquals(2, n.intValue());
		n = (Number) FunctionsTest.evaluate(Numbers.numberCast, "2");
		assertTrue(n instanceof Integer);
		assertEquals(2, n.intValue());
		n = (Number) FunctionsTest.evaluate(Numbers.numberCast, "2.5");
		assertTrue(n instanceof Float);
		assertEquals(2.5f, n.floatValue(), 0.01f);
		n = (Number) FunctionsTest.evaluate(Numbers.numberCast, 2.5f);
		assertTrue(n instanceof Float);
		assertEquals(2.5f, n.floatValue(), 0.01f);
		n = (Number) FunctionsTest.evaluate(Numbers.numberCast, 2.5d);
		assertTrue(n instanceof Double);
		assertEquals(2.5d, n.doubleValue(), 0.01d);
	}
	
	@Test(expected=FunctionException.class)
	public void testNumberCast2()
	{
		FunctionsTest.evaluate(Numbers.numberCast, new Object());
	}
	
	@Test(expected=FunctionException.class)
	public void testNumberCast3()
	{
		FunctionsTest.evaluate(Numbers.numberCast, "foo");
	}
	
	@Test
	public void testNumberCastDuplicate()
	{
		NumberCast nc = Numbers.numberCast.duplicate();
		assertTrue(nc == Numbers.numberCast);
	}
	
	@Test
	public void testSumPush() 
	{
		QueueSource cp = new QueueSource(1);
		cp.addEvent(1);
		Sum cs = new Sum();
		QueueSink qs = new QueueSink(1);
		Connector.connect(cp, cs);
		Connector.connect(cs, qs);
		Queue<Object> q = qs.getQueue(0);
		Number n;
		cp.push();
		n = (Number) q.remove();
		assertEquals(1, n.intValue());
		cp.push();
		n = (Number) q.remove();
		assertEquals(2, n.intValue());
		cp.push();
		n = (Number) q.remove();
		assertEquals(3, n.intValue());
	}
	
	@Test
	public void testSumPull() 
	{
		QueueSource cp = new QueueSource(1);
		cp.addEvent(1);
		Sum cs = new Sum();
		QueueSink qs = new QueueSink(1);
		Connector.connect(cp, cs);
		Connector.connect(cs, qs);
		Queue<Object> q = qs.getQueue(0);
		Number n;
		qs.pull();
		n = (Number) q.remove();
		if (n.intValue() != 1)
		{
			fail("Wrong number");
		}
		qs.pull();
		n = (Number) q.remove();
		if (n.intValue() != 2)
		{
			fail("Wrong number");
		}
		qs.pull();
		n = (Number) q.remove();
		if (n.intValue() != 3)
		{
			fail("Wrong number");
		}
	}
	
	@Test
	public void testStatisticalMomentPull1() 
	{
		Vector<Object> l_input1 = new Vector<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(2);
		QueueSource input1 = new QueueSource(1);
		input1.setEvents(l_input1);
		QueueSink sink = new QueueSink(1);
		setupStatisticalMoment(input1, sink, 1);
		Number recv;
		sink.pull();
		recv = (Number) sink.remove()[0]; // 2
		if (recv == null || Math.abs(recv.floatValue() - 2) > 0.0001)
		{
			fail("Expected 2, got " + recv);
		}
		sink.pull();
		recv = (Number) sink.remove()[0]; // 2
		if (recv == null || Math.abs(recv.floatValue() - 2.5) > 0.0001)
		{
			fail("Expected 2.5, got " + recv);
		}
		sink.pull();
		recv = (Number) sink.remove()[0]; // 2
		if (recv == null || Math.abs(recv.floatValue() - 2.33333) > 0.0001)
		{
			fail("Expected 2.33, got " + recv);
		} 
	}
	
	@Test
	public void testStatisticalMomentPush1() 
	{
		Vector<Object> l_input1 = new Vector<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(2);
		QueueSource input1 = new QueueSource(1);
		input1.setEvents(l_input1);
		QueueSink sink = new QueueSink(1);
		setupStatisticalMoment(input1, sink, 1);
		Number recv;
		input1.push();
		recv = (Number) sink.remove()[0]; // 2
		if (recv == null || Math.abs(recv.floatValue() - 2) > 0.0001)
		{
			fail("Expected 2, got " + recv);
		}
		input1.push();
		recv = (Number) sink.remove()[0]; // 2
		if (recv == null || Math.abs(recv.floatValue() - 2.5) > 0.0001)
		{
			fail("Expected 2.5, got " + recv);
		}
		input1.push();
		recv = (Number) sink.remove()[0]; // 2
		if (recv == null || Math.abs(recv.floatValue() - 2.33333) > 0.0001)
		{
			fail("Expected 2.33, got " + recv);
		} 
	}
	
	protected static void setupStatisticalMoment(Processor source, Processor sink, int n) 
	{
		Fork fork = new Fork(2);
		Connector.connect(source, fork);
		Sum sum_left = new Sum();
		{
			// Left part: sum of x^n
			Fork fork2 = new Fork(2);
			Connector.connect(fork, 0 ,fork2, 0);
			ReplaceWith exponent = new ReplaceWith(1);
			Connector.connect(fork2, 0, exponent, 0);
			ApplyFunction pow = new ApplyFunction(Numbers.power);
			Connector.connect(fork2, 1, pow, 0);
			Connector.connect(exponent, 0, pow, 1);
			Connector.connect(pow, sum_left);
		}
		Sum sum_right = new Sum();
		{
			// Right part: sum of 1
			ReplaceWith one = new ReplaceWith(1);
			Connector.connect(fork, 1, one, 0);
			Connector.connect(one, sum_right);
		}
		ApplyFunction div = new ApplyFunction(Numbers.division);
		Connector.connect(sum_left, 0, div, 0);
		Connector.connect(sum_right, 0, div, 1);
		Connector.connect(div, sink);
	}
	
	protected static void setupSumIfGreater(Processor source, Processor sink) 
	{
		Window win = new Window(new Sum(), 2);
		Connector.connect(source, win);
		Fork fork = new Fork(3);
		Connector.connect(win, fork);
		ApplyFunction greater = new ApplyFunction(Numbers.isGreaterThan);
		ReplaceWith five = new ReplaceWith(5);
		Connector.connect(fork, 0, five, 0);
		Connector.connect(fork, 1, greater, 0);
		Connector.connect(five, 0, greater, 1);
		Filter fil = new Filter();
		Connector.connect(fork, 2, fil, 0);
		Connector.connect(greater, 0, fil, 1);
		Connector.connect(fil, sink);
	}

	@Test
	public void testSumIfGreaterPush() 
	{
		Vector<Object> l_input1 = new Vector<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(0);
		l_input1.add(6);
		QueueSource input1 = new QueueSource(1);
		input1.setEvents(l_input1);
		QueueSink sink = new QueueSink(1);
		setupSumIfGreater(input1, sink);
		Number recv;
		input1.push();
		input1.push();
		recv = (Number) sink.remove()[0]; // 2+3=5, null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}
		input1.push();
		recv = (Number) sink.remove()[0]; // 3+4=7
		if (recv == null || recv.intValue() != 7)
		{
			fail("Expected 7, got " + recv);
		}
		input1.push();
		recv = (Number) sink.remove()[0]; // 4+0=4, null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}
		input1.push();
		recv = (Number) sink.remove()[0]; // 0+6=6
		if (recv == null || recv.intValue() != 6)
		{
			fail("Expected 6, got " + recv);
		}
	}
	
	@Test
	public void testSumIfGreaterPullHard() 
	{
		Vector<Object> l_input1 = new Vector<Object>();
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		l_input1.add(0);
		l_input1.add(6);
		QueueSource input1 = new QueueSource(1);
		input1.setEvents(l_input1);
		QueueSink sink = new QueueSink(1);
		setupSumIfGreater(input1, sink);
		Number recv;
		sink.pullHard();
		recv = (Number) sink.remove()[0]; // 3+4=7
		assertEquals(7, recv.intValue());
		sink.pullHard();
		recv = (Number) sink.remove()[0]; // 0+6=6
		assertEquals(6, recv.intValue());
	}
	
	public static class Sum extends Cumulate
	{
		@SuppressWarnings({ "rawtypes", "unchecked" })
		public Sum()
		{
			super(new CumulativeFunction(Numbers.addition));
		}
	}

}
