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
package ca.uqac.lif.cep.eml.tuples;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.eml.tuples.TupleGrammar;
import ca.uqac.lif.cep.interpreter.GrammarExtension;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;

public class TuplesEmlTest
{
	protected Interpreter m_interpreter;
	
	@Before
	public void setUp()
	{
		m_interpreter = new Interpreter();
		GrammarExtension ext = new TupleGrammar();
		m_interpreter.extendGrammar(ext);
	}
	
	@Test
	public void testExtension1() throws ParseException
	{
		String expression = "0";
		m_interpreter.setDebugMode(true);
		Object result = m_interpreter.parseLanguage(expression);
		assertNotNull(result);
		assertTrue(result instanceof EmlNumber);
	}
	
	@Test
	public void testExtension2() throws ParseException
	{
		String expression = "SELECT 0 FROM (0)";
		m_interpreter.setDebugMode(true);
		Object result = m_interpreter.parseLanguage(expression);
		assertNotNull(result);
		assertTrue(result instanceof Select);
	}
	

}
