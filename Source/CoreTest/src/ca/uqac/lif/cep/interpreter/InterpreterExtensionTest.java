/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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
import ca.uqac.lif.cep.CumulativeProcessor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.epl.CountDecimate;
import ca.uqac.lif.cep.epl.Freeze;
import ca.uqac.lif.cep.epl.Window;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.io.HttpReader;
import ca.uqac.lif.cep.io.StreamGrammar;
import ca.uqac.lif.cep.numbers.EmlNumber;
import ca.uqac.lif.cep.numbers.NumberGrammar;

/**
 * Unit tests for grammar extensions
 * @author Sylvain Hallé
 *
 */
public class InterpreterExtensionTest
{
	protected InterpreterTestFrontEnd m_interpreter;
	
	@Before
	public void setUp()
	{
		m_interpreter = new InterpreterTestFrontEnd();
		m_interpreter.extendGrammar(NumberGrammar.class);
		m_interpreter.extendGrammar(StreamGrammar.class);
	}
	
	@Test
	public void testExtensionNumber1() throws ParseException, ConnectorException
	{
		String expression = "0";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof EmlNumber);
		assertEquals(0, ((EmlNumber) result).intValue());
	}
	
	@Test
	public void testExtensionNumber2() throws ParseException, ConnectorException
	{
		String expression = "FREEZE (0)";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof Freeze);
		Pullable output = ((Freeze) result).getPullableOutput(0);
		Object o = output.pull();
		assertTrue(o instanceof EmlNumber);
	}
	
	@Test
	public void testExtensionNumber3() throws ParseException, ConnectorException
	{
		String expression = "APPLY (0) ON (0) ON A WINDOW OF 3";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof Window);
	}
	
	@Test
	public void testExtensionNumber4() throws ParseException, ConnectorException
	{
		String expression = "EVERY 2ND OF (0)";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof CountDecimate);
	}
	
	@Test
	public void testExtensionNumber5() throws ParseException, ConnectorException
	{
		String expression = "COMBINE (EVERY 2ND OF (0)) WITH ADDITION";
		Object result = m_interpreter.parseQuery(expression);
		assertNotNull(result);
		assertTrue(result instanceof CumulativeProcessor);
	}
	
	@Test
	public void testExtensionIo1() throws ParseException, ConnectorException
	{
		String expression = "URL \"http://example.com\"";
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
