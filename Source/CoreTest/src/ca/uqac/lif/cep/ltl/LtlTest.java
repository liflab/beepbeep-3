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
package ca.uqac.lif.cep.ltl;

import static org.junit.Assert.*;

import java.util.Vector;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.epl.QueueSource;
import ca.uqac.lif.cep.eml.tuples.EmlBoolean;
import ca.uqac.lif.cep.eml.tuples.TupleGrammar;
import ca.uqac.lif.cep.interpreter.InterpreterTestFrontEnd;
import ca.uqac.lif.cep.io.StreamGrammar;

public class LtlTest 
{
	protected InterpreterTestFrontEnd m_interpreter;

	@Before
	public void setUp()
	{
		m_interpreter = new InterpreterTestFrontEnd();		
		m_interpreter.extendGrammar(new StreamGrammar());
		m_interpreter.extendGrammar(new TupleGrammar());
		m_interpreter.extendGrammar(new LtlGrammar());
	}
	
	@Test
	public void testGlobally1()
	{
		QueueSource src = new QueueSource(null, 1);
		Vector<Object> input_events = new Vector<Object>();
		input_events.add(EmlBoolean.toEmlBoolean(true));
		input_events.add(EmlBoolean.toEmlBoolean(true));
		input_events.add(EmlBoolean.toEmlBoolean(false));
		input_events.add(EmlBoolean.toEmlBoolean(true));
		src.setEvents(input_events);
		Globally g = new Globally();
		Connector.connect(src, g);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertEquals(false, b.booleanValue());
		b = (Boolean) p.pull();
		assertEquals(false, b.booleanValue());
	}
	
	@Test
	public void testEventually1()
	{
		QueueSource src = new QueueSource(null, 1);
		Vector<Object> input_events = new Vector<Object>();
		input_events.add(EmlBoolean.toEmlBoolean(false));
		input_events.add(EmlBoolean.toEmlBoolean(false));
		input_events.add(EmlBoolean.toEmlBoolean(true));
		input_events.add(EmlBoolean.toEmlBoolean(false));
		src.setEvents(input_events);
		Eventually g = new Eventually();
		Connector.connect(src, g);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertNotNull(b);
		assertEquals(true, b.booleanValue());
		b = (Boolean) p.pull();
		assertEquals(true, b.booleanValue());
	}
	
	@Test
	public void testNext1()
	{
		QueueSource src = new QueueSource(null, 1);
		Vector<Object> input_events = new Vector<Object>();
		input_events.add(false);
		input_events.add(false);
		input_events.add(true);
		input_events.add(false);
		src.setEvents(input_events);
		Next g = new Next();
		Connector.connect(src, g);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertNotNull(b);
		assertEquals(false, b.booleanValue());
		b = (Boolean) p.pull();
		assertEquals(true, b.booleanValue());
	}
	
	@Test
	public void testNext2()
	{
		QueueSource src = new QueueSource(null, 1);
		Vector<Object> input_events = new Vector<Object>();
		input_events.add(EmlBoolean.toEmlBoolean(false));
		input_events.add(EmlBoolean.toEmlBoolean(true));
		input_events.add(EmlBoolean.toEmlBoolean(true));
		input_events.add(EmlBoolean.toEmlBoolean(false));
		src.setEvents(input_events);
		Next g = new Next();
		Connector.connect(src, g);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertNotNull(b);
		assertEquals(true, b.booleanValue());
	}
	
	@Test
	public void testNot()
	{
		QueueSource src = new QueueSource(null, 1);
		Vector<Object> input_events = new Vector<Object>();
		input_events.add(EmlBoolean.toEmlBoolean(false));
		input_events.add(EmlBoolean.toEmlBoolean(true));
		input_events.add(EmlBoolean.toEmlBoolean(true));
		input_events.add(EmlBoolean.toEmlBoolean(false));
		src.setEvents(input_events);
		Not g = new Not();
		Connector.connect(src, g);
		Pullable p = g.getPullableOutput(0);
		boolean b;
		b = (Boolean) p.pull();
		assertEquals(true, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
	}
	
	@Test
	public void testAnd1()
	{
		QueueSource src_left = new QueueSource(null, 1);
		QueueSource src_right = new QueueSource(null, 1);
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src_left.setEvents(input_events);
		}
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			src_right.setEvents(input_events);
		}
		And g = new And();
		Connector.connect(src_left, g, 0, 0);
		Connector.connect(src_right, g, 0, 1);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
	}
	
	@Test
	public void testAnd2()
	{
		QueueSource src_left = new QueueSource(null, 1);
		QueueSource src_right = new QueueSource(null, 1);
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			src_left.setEvents(input_events);
		}
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(null);
			input_events.add(EmlBoolean.toEmlBoolean(true));
			src_right.setEvents(input_events);
		}
		And g = new And();
		Connector.connect(src_left, g, 0, 0);
		Connector.connect(src_right, g, 0, 1);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
	}
	
	@Test
	public void testOr()
	{
		QueueSource src_left = new QueueSource(null, 1);
		QueueSource src_right = new QueueSource(null, 1);
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src_left.setEvents(input_events);
		}
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			src_right.setEvents(input_events);
		}
		Or g = new Or();
		Connector.connect(src_left, g, 0, 0);
		Connector.connect(src_right, g, 0, 1);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
	}
	
	@Test
	public void testUntil1()
	{
		QueueSource src_left = new QueueSource(null, 1);
		QueueSource src_right = new QueueSource(null, 1);
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src_left.setEvents(input_events);
		}
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			src_right.setEvents(input_events);
		}
		Until g = new Until();
		Connector.connect(src_left, g, 0, 0);
		Connector.connect(src_right, g, 0, 1);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
	}
	
	@Test
	public void testUntil2()
	{
		QueueSource src_left = new QueueSource(null, 1);
		QueueSource src_right = new QueueSource(null, 1);
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src_left.setEvents(input_events);
		}
		{
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src_right.setEvents(input_events);
		}
		Until g = new Until();
		Connector.connect(src_left, g, 0, 0);
		Connector.connect(src_right, g, 0, 1);
		Pullable p = g.getPullableOutput(0);
		Boolean b;
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
	}
	
	@Test
	public void testExpression1()
	{
		String expression = "(@T) AND (@U)";
		{
			QueueSource src = new QueueSource(null, 1);
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src.setEvents(input_events);
			m_interpreter.addPlaceholder("@T", "processor", src);
		}
		{
			QueueSource src = new QueueSource(null, 1);
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src.setEvents(input_events);
			m_interpreter.addPlaceholder("@U", "processor", src);
		}
		Pullable p = m_interpreter.executeQuery(expression);
		Boolean b;
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
		b = (Boolean) p.pull();
		assertEquals(false, b);
	}
	
	@Test
	public void testExpression2()
	{
		String expression = "(@T) AND (X (@U))";
		{
			QueueSource src = new QueueSource(null, 1);
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src.setEvents(input_events);
			m_interpreter.addPlaceholder("@T", "processor", src);
		}
		{
			QueueSource src = new QueueSource(null, 1);
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src.setEvents(input_events);
			m_interpreter.addPlaceholder("@U", "processor", src);
		}
		Pullable p = m_interpreter.executeQuery(expression);
		assertNotNull(p);
		Boolean b;
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
	}
	
	@Test
	public void testExpression3()
	{
		String expression = "X (@U)";
		{
			QueueSource src = new QueueSource(null, 1);
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src.setEvents(input_events);
			m_interpreter.addPlaceholder("@U", "processor", src);
		}
		Pullable p = m_interpreter.executeQuery(expression);
		assertNotNull(p);
		Boolean b;
		b = (Boolean) p.pull();
		assertNull(b);
		b = (Boolean) p.pull();
		assertEquals(true, b);
	}
	
	@Test
	public void testMultiline()
	{
		String expression = "(SELECT (a) LESS THAN (2) FROM (@P))\nAND\n(X (SELECT (a) GREATER THAN (1) FROM (@P)))";
		{
			QueueSource src = new QueueSource(null, 1);
			Vector<Object> input_events = new Vector<Object>();
			input_events.add(EmlBoolean.toEmlBoolean(false));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(true));
			input_events.add(EmlBoolean.toEmlBoolean(false));
			src.setEvents(input_events);
			m_interpreter.addPlaceholder("@P", "processor", src);
		}
		Pullable p = m_interpreter.executeQuery(expression);
		assertNotNull(p);
	}
}
