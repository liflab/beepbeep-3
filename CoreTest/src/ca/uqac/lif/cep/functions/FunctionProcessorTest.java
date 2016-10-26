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
package ca.uqac.lif.cep.functions;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the {@link FunctionProcessor}
 * 
 * @author Sylvain Hallé
 */
public class FunctionProcessorTest 
{
	protected Interpreter m_interpreter;
	
	@Before
	public void setup()
	{
		m_interpreter = new Interpreter();
	}
	
	@Test
	public void testFunctionProcessorGrammar1() throws ParseException
	{
		QueueSource source1 = createSource1();
		QueueSource source2 = createSource2();
		m_interpreter.addPlaceholder("@foo", "processor", source1);
		m_interpreter.addPlaceholder("@bar", "processor", source2);
		Processor proc = (Processor) m_interpreter.parseQuery("APPLY (($0) + ($1)) WITH (@foo) AS $A, (@bar) AS $B");
		Pullable p = proc.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof Number);
		assertEquals(5, ((Number) o).intValue());
		o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof Number);
		assertEquals(7, ((Number) o).intValue());
	}
	
	@Test
	public void testFunctionProcessorGrammar2() throws ParseException
	{
		QueueSource source1 = createSource1();
		QueueSource source2 = createSource2();
		m_interpreter.addPlaceholder("@foo", "processor", source1);
		m_interpreter.addPlaceholder("@bar", "processor", source2);
		Processor proc = (Processor) m_interpreter.parseQuery("APPLY (($A) + ($B)) WITH (@foo) AS $A, (@bar) AS $B");
		Pullable p = proc.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof Number);
		assertEquals(5, ((Number) o).intValue());
		o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof Number);
		assertEquals(7, ((Number) o).intValue());
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
