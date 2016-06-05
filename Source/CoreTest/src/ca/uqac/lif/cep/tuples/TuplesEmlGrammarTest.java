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
package ca.uqac.lif.cep.tuples;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.bullwinkle.BnfParser;
import ca.uqac.lif.bullwinkle.BnfParser.InvalidGrammarException;
import ca.uqac.lif.bullwinkle.ParseNode;
import ca.uqac.lif.cep.epl.EplGrammar;
import ca.uqac.lif.cep.interpreter.GrammarExtension;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.io.StreamGrammar;
import ca.uqac.lif.cep.numbers.NumberGrammar;
import ca.uqac.lif.cep.tuples.TupleGrammar;
import ca.uqac.lif.bullwinkle.BnfParser.ParseException;
import ca.uqac.lif.util.PackageFileReader;

public class TuplesEmlGrammarTest
{	
	protected BnfParser m_parser;

	@Before
	public void setUp()
	{
		try
		{
			m_parser = new BnfParser();
			m_parser.setGrammar(PackageFileReader.readPackageFile(Interpreter.class, "eml.bnf"));
			{
				GrammarExtension ext = new EplGrammar();
				String productions = ext.getGrammar();
				m_parser.setGrammar(productions);
			}
			{
				GrammarExtension ext = new NumberGrammar();
				String productions = ext.getGrammar();
				m_parser.setGrammar(productions);
			}
			{
				GrammarExtension ext = new StreamGrammar();
				String productions = ext.getGrammar();
				m_parser.setGrammar(productions);
			}
			{
				GrammarExtension ext = new TupleGrammar();
				String productions = ext.getGrammar();
				m_parser.setGrammar(productions);
			}

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
		ParseNode result = shouldParse(expression, "<eml_number>");
		assertEquals("<eml_number>", result.getValue());
	}

	@Test
	public void testExtension2() throws ParseException
	{
		String expression = "SELECT p FROM (0)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension3() throws ParseException
	{
		String expression = "SELECT q AS p FROM (0)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension4a() throws ParseException
	{
		String expression = "SELECT q FROM (0 AS t1)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension4b() throws ParseException
	{
		String expression = "SELECT q AS att FROM (0 AS t1)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension5() throws ParseException
	{
		String expression = "SELECT 0 AS att FROM 0 AS";
		shouldNotParse(expression, "<eml_select>");
	}

	@Test
	public void testExtension6() throws ParseException
	{
		String expression = "SELECT 0 AS att FROM (0 AS t1, 1 AS t2)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension7() throws ParseException
	{
		String expression = "SELECT 0 AS att, 1 AS att2 FROM (0 AS t1)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension8() throws ParseException
	{
		String expression = "SELECT (0) + (1) AS att, 1 AS att2 FROM (0 AS t1)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension9() throws ParseException
	{
		String expression = "SELECT t1.p AS att, 1 AS att2 FROM (0 AS t1)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension10() throws ParseException
	{
		String expression = "SELECT t1.p AS att, \"tango\" AS att2 FROM (0 AS t1, (SELECT p FROM (0)) AS t3)";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension11() throws ParseException
	{
		String expression = "SELECT p FROM (SELECT q FROM (0))";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension12() throws ParseException
	{
		String expression = "SELECT p FROM (SELECT q FROM (0))";
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}

	@Test
	public void testExtension13() throws ParseException
	{
		String expression = "0";
		ParseNode result = shouldParse(expression, "<eml_att_expr>");
		assertEquals("<eml_att_expr>", result.getValue());
	}

	@Test
	public void testExtension14() throws ParseException
	{
		String expression = "(0) WHERE (a) = (b)";
		ParseNode result = shouldParse(expression, "<eml_where>");
		assertEquals("<eml_where>", result.getValue());
	}

	@Test
	public void testExtension15a() throws ParseException
	{
		String expression = "(THE TUPLES OF FILE \"tuples1.csv\") WHERE (a) = (0)";
		m_parser.setDebugMode(false);
		ParseNode result = shouldParse(expression, "<eml_where>");
		assertEquals("<eml_where>", result.getValue());
	}

	@Test
	public void testExtension15b() throws ParseException
	{
		String expression = "(THE TUPLES OF FILE \"tuples1.csv\") WHERE (a) = (0)";
		ParseNode result = shouldParse(expression, "<processor>");
		assertEquals("<processor>", result.getValue());
	}
	
	@Test
	public void testExtension16() throws ParseException
	{
		String expression = "COMBINE (SELECT x FROM (0)) WITH ADDITION";
		ParseNode result = shouldParse(expression, "<processor>");
		assertEquals("<processor>", result.getValue());
	}
	
	@Test
	public void testExtension17a() throws ParseException
	{
		String expression = "SELECT q FROM (((0) WHERE (a) = (\"MSFT\")))";
		m_parser.setDebugMode(false);
		ParseNode result = shouldParse(expression, "<eml_select>");
		assertEquals("<eml_select>", result.getValue());
	}
	
	@Test
	public void testExtension18() throws ParseException
	{
		String expression = "(0) WHERE (*) = (0)";
		m_parser.setDebugMode(false);
		ParseNode result = shouldParse(expression, "<eml_where>");
		assertEquals("<eml_where>", result.getValue());
	}

	protected ParseNode shouldParse(String expression, String start_symbol) throws ParseException
	{
		m_parser.setStartRule(start_symbol);
		ParseNode pn = m_parser.parse(expression);
		assertNotNull("The parsing of " + expression + " has failed", pn);
		return pn;
	}

	protected ParseNode shouldNotParse(String expression, String start_symbol) throws ParseException
	{
		m_parser.setStartRule(start_symbol);
		ParseNode pn = m_parser.parse(expression);
		assertNull(pn);
		return pn;
	}


}
