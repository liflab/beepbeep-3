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

import ca.uqac.lif.cep.eml.tuples.TupleGrammar;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;

public class UserDefinitionTest 
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
	public void testDefinition1() throws ParseException
	{
		String expression = "WHEN @P IS A processor: THE COUNT OF (@P) IS THE processor SELECT x FROM (@P).";
		//m_interpreter.m_parser.setStartRule("<processor_def>");
		Object o = m_interpreter.parseLanguage(expression);
		assertNotNull(o);
		assertTrue(o instanceof UserDefinition);
		UserDefinition user_def = (UserDefinition) o;
		user_def.addToInterpreter(m_interpreter);
		// Now, parse an expression that uses this definition
		m_interpreter.setDebugMode(true);
		String user_expression = "THE COUNT OF (0)";
		m_interpreter.parseLanguage(user_expression);
	}
}
