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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Queue;
import java.util.Vector;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.numbers.NumberCast;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Window;

/**
 * Unit tests for ESQL user definitions
 * @author Sylvain Hallé
 *
 */
public class UserDefinitionTest extends BeepBeepUnitTest 
{
	protected Interpreter m_interpreter;

	@Before
	public void setUp()
	{
		m_interpreter = new Interpreter();
	}
	
	@Test
	public void testPlaceholder1() throws ParseException, ConnectorException
	{
		String expression = "@P";
		QueueSource qs = new QueueSource(1);
		qs.addEvent(1);
		m_interpreter.addPlaceholder("@P", "processor", qs);
		Object o = m_interpreter.parseQuery(expression);
		assertNotNull(o);
		assertTrue(o instanceof Processor);	
		Processor s = (Processor) o;
		Pullable p = s.getPullableOutput(0);
		Number n = (Number) p.pull();
		assertNotNull(n);
		assertEquals(1, n.intValue());
		n = (Number) p.pull();
		assertNotNull(n);
		assertEquals(1, n.intValue());
	}
	
	@Test
	public void testPlaceholder3() throws ParseException, ConnectorException
	{
		String expression = "abc IS THE processor @P";
		QueueSource qs = new QueueSource(1);
		qs.addEvent(1);
		m_interpreter.executeQuery(expression);
		m_interpreter.addPlaceholder("@P", "processor", qs);
		Object o = m_interpreter.parseQuery("abc");
		assertNotNull(o);
		assertTrue(o instanceof Processor);	
		Processor s = (Processor) o;
		Pullable p = s.getPullableOutput(0);
		Number n = (Number) p.pull();
		assertNotNull(n);
		assertEquals(1, n.intValue());
	}
	
	@Test
	public void testDefinition1() throws ParseException, ConnectorException
	{
		String expression = "WHEN @P IS A processor: THE COUNT OF ( @P ) IS THE processor CONSTANT (1)";
		Object o = m_interpreter.parseQuery(expression);
		assertNotNull(o);
		assertTrue(o instanceof UserDefinition);
		UserDefinition user_def = (UserDefinition) o;
		user_def.addToInterpreter(m_interpreter);
		QueueSource qs = new QueueSource();
		qs.addEvent(10);
		m_interpreter.addPlaceholder("@foo", "processor", qs);
		// Now, parse an expression that uses this definition
		String user_expression = "THE COUNT OF (@foo)";
		//m_interpreter.setDebugMode(true);
		Object user_stmt = m_interpreter.parseQuery(user_expression);
		assertNotNull(user_stmt);
		assertTrue(user_stmt instanceof Processor);
		Pullable p = ((Processor) user_stmt).getPullableOutput(0);
		// Pull a tuple from the resulting processor
		Object answer = p.pullSoft();
		assertNotNull(answer);
		assertTrue(answer instanceof Number);
		Number num = (Number) answer;
		assertEquals(1, num.intValue());
		// Pull another
		num = (Number) p.pullSoft();
		assertEquals(1, num.intValue());
		// Pull another
		num = (Number) p.pullSoft();
		assertEquals(1, num.intValue());
	}
	
	@Test
	public void testDefinition2() throws ParseException, ConnectorException
	{
		String expression = "PI IS THE eml_number 3.1416";
		Object o = m_interpreter.parseQuery(expression);
		assertNotNull(o);
		assertTrue(o instanceof UserDefinition);
		UserDefinition user_def = (UserDefinition) o;
		user_def.addToInterpreter(m_interpreter);
		// Now, parse an expression that uses this definition
		String user_expression = "CONSTANT (PI)";
		Object user_stmt = m_interpreter.parseQuery(user_expression);
		assertTrue(user_stmt instanceof Processor);
		Pullable p = ((Processor) user_stmt).getPullableOutput(0);
		// Pull a tuple from the resulting processor
		Object answer = p.pullSoft();
		assertNotNull(answer);
		assertTrue(answer instanceof Number);
		Number num = (Number) answer;
		assertEquals(3.1416, num.floatValue(), 0.01);
		// Pull another
		num = (Number) p.pullSoft();
		assertEquals(3.1416, num.floatValue(), 0.01);
	}
	
	@Test
	public void testDefinition5() throws ParseException, ConnectorException
	{
		{
			UserDefinition e_def = (UserDefinition) m_interpreter.parseQuery("WHEN @P IS A processor: THE COUNT OF ( @P ) IS THE processor COMBINE (CONSTANT (1)) WITH ADDITION");
			e_def.addToInterpreter(m_interpreter);
		}
		{
			UserDefinition e_def = (UserDefinition) m_interpreter.parseQuery("WHEN @P IS A processor: THE AVERAGE OF ( @P ) IS THE processor APPLY (($T) ÷ ($U)) WITH (COMBINE (@P) WITH ADDITION) AS $T, (THE COUNT OF (@P)) AS $U");
			e_def.addToInterpreter(m_interpreter);
		}
		QueueSource qs = new QueueSource();
		qs.setEvents(new Integer[]{0, 1, 2, 3, 4});
		m_interpreter.addPlaceholder("@foo", "processor", qs);
		Processor proc = (Processor) m_interpreter.parseQuery("THE AVERAGE OF (@foo)");
		assertNotNull(proc);
		Pullable p = proc.getPullableOutput(0);
		Number number = (Number) p.pullSoft();
		assertEquals(0, number.floatValue(), 0.01);
		number = (Number) p.pullSoft();
		assertEquals(0.5, number.floatValue(), 0.01);
		number = (Number) p.pullSoft();
		assertEquals(1, number.floatValue(), 0.01);
		number = (Number) p.pullSoft();
		//assertEquals(2, number.floatValue(), 0.01);
	}
	
	@Test
	public void testDefinition7() throws ParseException, ConnectorException
	{
		{
			UserDefinition e_def = (UserDefinition) m_interpreter.parseQuery("WHEN @P IS A processor: THE SUM OF ( @P ) IS THE processor COMBINE (@P) WITH ADDITION");
			e_def.addToInterpreter(m_interpreter);
		}
		QueueSource qs = new QueueSource(1);
		qs.addEvent(1);
		m_interpreter.addPlaceholder("@T", "processor", qs);
		Processor proc = (Processor) m_interpreter.parseQuery("APPLY (THE SUM OF (*)) ON (@T) ON A WINDOW OF 5");
		assertNotNull(proc);
		assertTrue(proc instanceof Window);
		Pullable p = proc.getPullableOutput();
		assertNotNull(p);
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof Number);
		float n = NumberCast.getNumber(o).floatValue();
		assertEquals(5, n, 0.01);
	}
	
	@Test
	public void testDefinition8() throws ParseException, ConnectorException
	{
		{
			UserDefinition e_def = (UserDefinition) m_interpreter.parseQuery("WHEN @P IS A processor, @N IS A number: FOO ( @P ) BAR @N IS THE processor TRIM @N OF (@P)");
			e_def.addToInterpreter(m_interpreter);
		}
		QueueSource qs = new QueueSource(1);
		Vector<Object> events = new Vector<Object>();
		events.add(0);
		events.add(1);
		events.add(2);
		qs.setEvents(events);
		m_interpreter.addPlaceholder("@T", "processor", qs);
		Processor proc = (Processor) m_interpreter.parseQuery("FOO (@T) BAR 2");
		assertNotNull(proc);
		QueueSink qsink = new QueueSink(1);
		Connector.connect(proc, qsink);
		Queue<Object> queue = qsink.getQueue(0);
		qsink.pullHard();
		assertFalse(queue.isEmpty());
		int i = ((Number) queue.remove()).intValue();
		assertEquals(2, i);
		assertNotNull(m_interpreter.toString());
	}
	
	@Test
	public void testDefinitionFunction1() throws ParseException, ConnectorException
	{
		m_interpreter.executeQuery("WHEN @X IS A function: FOO ( @X ) IS THE function ( ( @X ) + ( @X ) )");
		Object o = m_interpreter.parseLanguage("FOO (2)", "<function>");
		assertNotNull(o);
	}
	
	@Test
	public void testDefinitionFunction2() throws ParseException, ConnectorException
	{
		m_interpreter.executeQuery("WHEN @X IS A function, @Y IS A function: THE MODULUS OF ( @X , @Y ) IS THE function (((@X) ^ (2)) + ((@Y) ^ (2)))");
		//m_interpreter.addPlaceholder("@foo", "<processor>", object)
		//m_interpreter.executeQuery("FOO");
	}
	
}
