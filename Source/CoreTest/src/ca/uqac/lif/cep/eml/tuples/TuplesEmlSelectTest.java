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

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.GrammarExtension;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;

public class TuplesEmlSelectTest
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
	public void testSelect1() throws ParseException
	{
		Object processor = m_interpreter.parseLanguage("SELECT 0 FROM 0");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof EmlNumber);
		EmlNumber n = (EmlNumber) answer;
		assertEquals(0, n.numberValue().intValue());
	}
	
	@Test
	public void testSelect2() throws ParseException
	{
		Object processor = m_interpreter.parseLanguage("SELECT z FROM 0");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof EmlNumber);
		EmlNumber n = (EmlNumber) answer;
		assertEquals(0, n.numberValue().intValue());
	}
	
	@Test
	public void testSelect3() throws ParseException
	{
		Object processor = m_interpreter.parseLanguage("SELECT t.z FROM 0 AS t");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof EmlNumber);
		EmlNumber n = (EmlNumber) answer;
		assertEquals(0, n.numberValue().intValue());
	}
	
	@Test
	public void testSelect4() throws ParseException
	{
		Object processor = m_interpreter.parseLanguage("SELECT u.z FROM 1 AS t, 2 AS u");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof EmlNumber);
		EmlNumber n = (EmlNumber) answer;
		assertEquals(2, n.numberValue().intValue());
	}
	
	@Test
	public void testSelect5() throws ParseException
	{
		Object processor = m_interpreter.parseLanguage("SELECT (u.z) + (t.z) FROM 1 AS t, 2 AS u");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof EmlNumber);
		EmlNumber n = (EmlNumber) answer;
		assertEquals(3, n.numberValue().intValue());
	}
	
	@Test
	public void testSelect6() throws ParseException
	{
		Object processor = m_interpreter.parseLanguage("SELECT u.z AS w FROM 1 AS t, 2 AS u");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof NamedTuple);
		NamedTuple tup = (NamedTuple) answer;
		assertEquals(1, tup.keySet().size());
		assertEquals(2, ((EmlNumber) tup.get("w")).numberValue().intValue());
	}
}
