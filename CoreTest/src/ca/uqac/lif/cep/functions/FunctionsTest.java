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
package ca.uqac.lif.cep.functions;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.numbers.Division;

/**
 * Unit tests for functions
 */
public class FunctionsTest
{
	@Test
	public void testNegation() throws FunctionException
	{
		assertEquals(false, evaluate(Negation.instance, true));
		assertEquals(true, evaluate(Negation.instance, false));
	}
	
	@Test
	public void testOr() throws FunctionException
	{
		assertEquals(true, evaluate(Or.instance, true, false));
		assertEquals(false, evaluate(Or.instance, false, false));
	}
	
	@Test
	public void testException() throws FunctionException
	{
		boolean got_exception = false;
		try
		{
			evaluate(new ExceptionFunction(), 3);
		}
		catch (FunctionException e)
		{
			got_exception = true;
			assertNotNull(e.getMessage());
		}
		assertTrue(got_exception);
	}
	
	@Test
	public void testId() throws FunctionException
	{
		IdentityFunction f = new IdentityFunction(1);
		assertEquals(false, evaluate(f, false));
		assertEquals(0, evaluate(f, 0));
		assertEquals(1, f.getInputArity());
		assertEquals(1, f.getOutputArity());
		IdentityFunction f2 = f.duplicate();
		assertEquals(6, evaluate(f2, 6));
		assertEquals(1, f2.getInputArity());
		assertEquals(1, f2.getOutputArity());
		assertEquals(Variant.class, f.getOutputTypeFor(0));
		Set<Class<?>> types = new HashSet<Class<?>>();
		f.getInputTypesFor(types, 0);
		assertEquals(1, types.size());
		assertTrue(types.contains(Variant.class));
	}
	
	@Test
	public void testAnd() throws FunctionException
	{
		assertEquals(false, evaluate(And.instance, true, false));
		assertEquals(true, evaluate(And.instance, true, true));
	}
	
	@Test
	public void testContext1() throws FunctionException
	{
		Context c = new Context();
		c.put("a", 6);
		ContextPlaceholder cph = new ContextPlaceholder("a");
		assertEquals(6, evaluate(cph, c, true, true));
	}
	
	@Test
	public void testContext2() throws FunctionException
	{
		Context c = new Context();
		c.put("a", 6);
		FunctionTree f = new FunctionTree(Addition.instance, new Constant(3), new ContextPlaceholder("a"));
		assertEquals(9f, evaluate(f, c, 4));
	}
	
	@Test
	public void testFunctionTree1() throws FunctionException
	{
		FunctionTree ft = new FunctionTree(Addition.instance, new Constant(1), new ArgumentPlaceholder(0));
		assertEquals(6f, evaluate(ft, 5));
	}
	
	@Test
	public void testEvaluateFast() throws FunctionException
	{
		assertEquals(evaluateFast(And.instance, true, false), evaluate(And.instance, true, false));
	}
	
	
	public static Object evaluate(Function f, Context c, Object ... inputs) throws FunctionException
	{
		Object[] ins = inputs;
		Object[] out = new Object[1];
		f.evaluate(ins, out, c);
		return out[0];
	}
	
	public static Object evaluate(Function f, Object ... inputs) throws FunctionException
	{
		Object[] ins = inputs;
		Object[] out = new Object[1];
		f.evaluate(ins, out);
		return out[0];
	}
	
	public static Object evaluateFast(Function f, Object ... inputs) throws FunctionException
	{
		Object[] ins = inputs;
		Object[] out = new Object[1];
		f.evaluateFast(ins, out, null);
		return out[0];
	}
	
	public static class ExceptionFunction extends UnaryFunction<Number,Number>
	{
		public ExceptionFunction()
		{
			super(Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x) throws FunctionException 
		{
			throw new FunctionException("foo");
		}
	}
}
