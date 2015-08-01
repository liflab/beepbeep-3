/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.interpreter;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.CountDecimate;
import ca.uqac.lif.cep.Freeze;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Window;
import ca.uqac.lif.cep.eml.numbers.EmlNumber;
import ca.uqac.lif.cep.eml.numbers.NumberGrammar;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;

public class InterpreterExtensionTest
{
	protected Interpreter m_interpreter;
	
	@Before
	public void setUp()
	{
		m_interpreter = new Interpreter();
		GrammarExtension ext = new NumberGrammar();
		m_interpreter.extendGrammar(ext);
	}
	
	@Test
	public void testExtensionNumber1() throws ParseException
	{
		String expression = "0";
		Object result = m_interpreter.parseLanguage(expression);
		assertNotNull(result);
		assertTrue(result instanceof EmlNumber);
		assert(((EmlNumber) result).intValue() == 0);
	}
	
	@Test
	public void testExtensionNumber2() throws ParseException
	{
		String expression = "FREEZE 0";
		Object result = m_interpreter.parseLanguage(expression);
		assertNotNull(result);
		assertTrue(result instanceof Freeze);
		Pullable output = ((Freeze) result).getPullableOutput(0);
		Object o = output.pull();
		assertTrue(o instanceof EmlNumber);
	}
	
	@Test
	public void testExtensionNumber3() throws ParseException
	{
		String expression = "(0) ON A WINDOW OF 3";
		Object result = m_interpreter.parseLanguage(expression);
		assertNotNull(result);
		assertTrue(result instanceof Window);
	}
	
	@Test
	public void testExtensionNumber4() throws ParseException
	{
		String expression = "EVERY 2ND OF (0)";
		Object result = m_interpreter.parseLanguage(expression);
		assertNotNull(result);
		assertTrue(result instanceof CountDecimate);
	}
}
