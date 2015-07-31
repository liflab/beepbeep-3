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

import ca.uqac.lif.bullwinkle.BnfParser;
import ca.uqac.lif.bullwinkle.BnfParser.InvalidGrammarException;
import ca.uqac.lif.bullwinkle.ParseNode;
import ca.uqac.lif.cep.eml.tuples.TupleGrammar;
import ca.uqac.lif.cep.interpreter.GrammarExtension;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.util.PackageFileReader;

public class TuplesEmlTest
{	
	protected BnfParser m_parser;
	
	@Before
	public void setUp()
	{
		try
		{
			m_parser.setGrammar(PackageFileReader.readPackageFile(Interpreter.class, "eml.bnf"));		
			GrammarExtension ext = new TupleGrammar();
			String productions = ext.getGrammar();
			m_parser.setGrammar(productions);
		}
		catch (InvalidGrammarException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	@Test
	public void testExtension1() throws ParseException
	{
		String expression = "0";
		Object result = m_parser.parse(expression);
		assertNotNull(result);
		assertTrue(result instanceof EmlNumber);
	}
	
	@Test
	public void testExtension2() throws ParseException
	{
		String expression = "SELECT 0 FROM 0";
		Object result = shouldParse(expression, "<eml_select>");
		assertNotNull(result);
		assertTrue(result instanceof Select);
	}
	
	protected void shouldParse(String expression, String start_symbol) throws ParseException
	{
		ParseNode pn = m_parser.parse(expression);
	}
	

}
