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
package ca.uqac.lif.cep.interpreter;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.functions.CumulativeProcessor;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.io.HttpReader;
import ca.uqac.lif.cep.numbers.NumberCast;
import ca.uqac.lif.cep.tmf.CountDecimate;
import ca.uqac.lif.cep.tmf.Freeze;
import ca.uqac.lif.cep.tmf.Window;

/**
 * Unit tests for grammar extensions
 * @author Sylvain Hallé
 *
 */
public class InterpreterExtensionTest extends BeepBeepUnitTest
{
	protected Interpreter m_interpreter;
	
	@Before
	public void setUp()
	{
		m_interpreter = new Interpreter();
	}
	
	@Test
	public void testExtensionNumber1() throws ParseException, ConnectorException
	{
		String expression = "CONSTANT (0)";
		//m_interpreter.setDebugMode(true);
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof FunctionProcessor);
		Pullable p = ((FunctionProcessor) result).getPullableOutput();
		Object o = p.pull();
		assertEquals(0, NumberCast.getNumber(o).intValue());
	}
	
	@Test
	public void testExtensionNumber2() throws ParseException, ConnectorException
	{
		String expression = "FREEZE (CONSTANT (0))";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof Freeze);
		Pullable output = ((Freeze) result).getPullableOutput(0);
		Object o = output.pullSoft();
		assertTrue(o instanceof Number);
	}
	
	/*
	 * This tests a grammar extension on
	 * a syntactically valid, but semantically invalid query. One cannot
	 * apply a constant on a window. It will fail if checkBounds is set to
	 * true on Connector.
	 */
	@Test
	public void testExtensionNumber3() throws ParseException, ConnectorException
	{
		String expression = "APPLY (CONSTANT (0)) ON (CONSTANT (0)) ON A WINDOW OF 3";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof Window);
	}
	
	@Test
	public void testExtensionNumber4() throws ParseException, ConnectorException
	{
		String expression = "EVERY 2ND OF (CONSTANT (0))";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof CountDecimate);
	}
	
	@Test
	public void testExtensionNumber5() throws ParseException, ConnectorException
	{
		String expression = "COMBINE (EVERY 2ND OF (CONSTANT (1))) WITH ADDITION";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof CumulativeProcessor);
		Pullable p = ((Processor) result).getPullableOutput();
		int i = 0;
		i = ((Number) p.pull()).intValue();
		assertEquals(1, i);
		i = ((Number) p.pull()).intValue();
		assertEquals(2, i);
		i = ((Number) p.pull()).intValue();
		assertEquals(3, i);
		
	}
	
	@Test
	public void testExtensionIo1() throws ParseException, ConnectorException
	{
		String expression = "URL \"http://example.com\"";
		//m_interpreter.setDebugMode(true);
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof HttpReader);
	}
	
	@Test
	public void testPlaceholder() throws ParseException, ConnectorException
	{
		String expression = "*";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof Placeholder);
	}
}
