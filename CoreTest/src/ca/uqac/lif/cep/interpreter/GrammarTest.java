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

import static org.junit.Assert.*;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.util.FileHelper;
import ca.uqac.lif.cep.util.PackageFileReader;

public class GrammarTest 
{
	
	static String[] s_queries;

	protected Interpreter m_interpreter;

	@Before
	public void setup() throws IOException
	{
		m_interpreter = new Interpreter();
		String file_contents = PackageFileReader.readPackageFile(GrammarTest.class.getResourceAsStream("all-queries.esql"));
		s_queries = file_contents.split("---");
	}

	/*
	 * Simply run the parser on each string and make sure it does not fail 
	 */
	@Test
	public void parsingTest() throws ParseException
	{
		for (int i = 0; i < s_queries.length; i++)
		{
			String query = s_queries[i];
			query = query.trim();
			if (query.isEmpty())
			{
				continue;
			}
			m_interpreter.reset();
			m_interpreter.addPlaceholder("@foo", "processor", new QueueSource());
			m_interpreter.addPlaceholder("@bar", "processor", new QueueSource());
			Pullable p = m_interpreter.executeQueries(query);
			if (p == null)
			{
				fail("Parsing failed on expression " + query);
			}
		}
	}
	
	@Test
	public void debugQueryNumber() throws ParseException
	{
		int n = 6;
		String query = s_queries[n];
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(baos);
		m_interpreter.setDebugMode(true, ps);
		m_interpreter.addPlaceholder("@foo", "processor", new QueueSource());
		m_interpreter.addPlaceholder("@bar", "processor", new QueueSource());
		try
		{
			Pullable p = m_interpreter.executeQueries(query);
			if (p == null)
			{
				fail("Parsing failed on expression " + query);
			}
		}
		catch (ParseException e)
		{
			FileHelper.writeFromBytes(new File("/home/sylvain/debug.txt"), baos.toByteArray());
			throw e;
		}
	}
}
