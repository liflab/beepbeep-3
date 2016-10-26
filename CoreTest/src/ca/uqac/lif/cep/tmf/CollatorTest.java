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
package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.util.CacheMap;

/**
 * Unit tests for the Collator
 * 
 * @author Sylvain Hallé
 */
public class CollatorTest
{
	protected Interpreter m_interpreter;
	
	@Before
	public void setup()
	{
		m_interpreter = new Interpreter();
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testCollator1() throws ConnectorException
	{
		QueueSource source1 = createSource1();
		ProcessorExpressionList pel = new ProcessorExpressionList();
		pel.add(new ProcessorExpression(source1, "$A"));
		Collator col = new Collator(pel);
		Connector.connect(source1, col);
		Pullable p = col.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof CacheMap);
		CacheMap<Object> map = (CacheMap<Object>) o;
		assertEquals(0, map.getIndexOf("$A"));
		assertEquals(-1, map.getIndexOf("$B"));
		Object mv = map.getValue(0);
		assertTrue(mv instanceof Number);
		assertEquals(0, ((Number) mv).intValue());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testCollator2() throws ConnectorException
	{
		QueueSource source1 = createSource1();
		QueueSource source2 = createSource2();
		ProcessorExpressionList pel = new ProcessorExpressionList();
		pel.add(new ProcessorExpression(source1, "$A"));
		pel.add(new ProcessorExpression(source2, "$B"));
		Collator col = new Collator(pel);
		Connector.connect(source1, 0, col, 0);
		Connector.connect(source2, 0, col, 1);
		Pullable p = col.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof CacheMap);
		CacheMap<Object> map = (CacheMap<Object>) o;
		assertEquals(0, map.getIndexOf("$A"));
		assertEquals(1, map.getIndexOf("$B"));
		Object mv;
		mv = map.getValue(0);
		assertTrue(mv instanceof Number);
		assertEquals(0, ((Number) mv).intValue());
		mv = map.getValue(1);
		assertTrue(mv instanceof Number);
		assertEquals(5, ((Number) mv).intValue());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testCollatorGrammar1() throws ParseException
	{
		QueueSource source1 = createSource1();
		m_interpreter.addPlaceholder("@foo", "processor", source1);
		Processor proc = (Processor) m_interpreter.parseQuery("WITH (@foo) AS $A");
		Pullable p = proc.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof CacheMap);
		CacheMap<Object> map = (CacheMap<Object>) o;
		assertEquals(0, map.getIndexOf("$A"));
		assertEquals(-1, map.getIndexOf("$B"));
		Object mv = map.getValue(0);
		assertTrue(mv instanceof Number);
		assertEquals(0, ((Number) mv).intValue());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testCollatorGrammar2() throws ParseException
	{
		QueueSource source1 = createSource1();
		QueueSource source2 = createSource2();
		m_interpreter.addPlaceholder("@foo", "processor", source1);
		m_interpreter.addPlaceholder("@bar", "processor", source2);
		Processor proc = (Processor) m_interpreter.parseQuery("WITH (@foo) AS $A, (@bar) AS $B");
		Pullable p = proc.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof CacheMap);
		CacheMap<Object> map = (CacheMap<Object>) o;
		assertEquals(0, map.getIndexOf("$A"));
		assertEquals(1, map.getIndexOf("$B"));
		Object mv;
		mv = map.getValue(0);
		assertTrue(mv instanceof Number);
		assertEquals(0, ((Number) mv).intValue());
		mv = map.getValue(1);
		assertTrue(mv instanceof Number);
		assertEquals(5, ((Number) mv).intValue());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testCollatorGrammar3() throws ParseException
	{
		QueueSource source1 = createSource1();
		m_interpreter.addPlaceholder("@foo", "processor", source1);
		Processor proc = (Processor) m_interpreter.parseQuery("WITH (@foo)");
		Pullable p = proc.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof CacheMap);
		CacheMap<Object> map = (CacheMap<Object>) o;
		Object mv = map.getValue(0);
		assertTrue(mv instanceof Number);
		assertEquals(0, ((Number) mv).intValue());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testCollatorGrammar4() throws ParseException
	{
		QueueSource source1 = createSource1();
		QueueSource source2 = createSource2();
		m_interpreter.addPlaceholder("@foo", "processor", source1);
		m_interpreter.addPlaceholder("@bar", "processor", source2);
		Processor proc = (Processor) m_interpreter.parseQuery("WITH (@foo), (@bar)");
		Pullable p = proc.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof CacheMap);
		CacheMap<Object> map = (CacheMap<Object>) o;
		Object mv;
		mv = map.getValue(0);
		assertTrue(mv instanceof Number);
		assertEquals(0, ((Number) mv).intValue());
		mv = map.getValue(1);
		assertTrue(mv instanceof Number);
		assertEquals(5, ((Number) mv).intValue());
	}
	
	/**
	 * Creates a dummy source of events
	 * @return
	 */
	public static QueueSource createSource1()
	{
		QueueSource qs = new QueueSource();
		qs.setEvents(new Integer[]{0, 1, 2, 3, 4});
		return qs;
	}
	
	/**
	 * Creates a dummy source of events
	 * @return
	 */
	public static QueueSource createSource2()
	{
		QueueSource qs = new QueueSource();
		qs.setEvents(new Integer[]{5, 6, 7, 8, 9});
		return qs;
	}
}
