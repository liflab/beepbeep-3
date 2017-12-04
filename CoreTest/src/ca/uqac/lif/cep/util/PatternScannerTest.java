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
package ca.uqac.lif.cep.util;

import static org.junit.Assert.*;

import java.util.Queue;
import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.util.FindPattern;

/**
 * Unit tests for the {@link FindPattern} class 
 * @author Sylvain Hallé
 */
public class PatternScannerTest 
{
	@Test
	public void testPatternScanner1()
	{
		QueueSource qs = new QueueSource();
		qs.setEvents(new Object[]{"123", "45", "67"});
		qs.loop(false);
		FindPattern ps  = new FindPattern("\\d");
		Connector.connect(qs, ps);
		Pullable p = ps.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals("1", p.next());
		assertTrue(p.hasNext());
		assertEquals("2", p.next());
		assertTrue(p.hasNext());
		assertEquals("3", p.next());
	}
	
	@Test
	public void testPatternScanner2()
	{
		QueueSource qs = new QueueSource();
		qs.setEvents(new Object[]{"A0B", "A1", "BA2B"});
		qs.loop(false);
		FindPattern ps  = new FindPattern("A.*?B");
		Connector.connect(qs, ps);
		Pullable p = ps.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals("A0B", p.next());
		assertTrue(p.hasNext());
		assertEquals("A1B", p.next());
		assertTrue(p.hasNext());
		assertEquals("A2B", p.next());
	}
	
	@Test
	public void testPatternScannerPush1() 
	{
		String s;
		FindPattern mf = new FindPattern("\\|.*?\\.");
		QueueSink qsink = new QueueSink(1);
		Queue<Object> queue = qsink.getQueue(0);
		Connector.connect(mf, qsink);
		Pushable in = mf.getPushableInput(0);
		in.push("|hello.|hi.");
		assertEquals(2, queue.size());
		s = (String) queue.remove();
		assertEquals("|hello.", s);
		s = (String) queue.remove();
		assertEquals("|hi.", s);
	}
	
	@Test
	public void testPatternScannerPush2() 
	{
		String s;
		FindPattern mf = new FindPattern("\\|.*?\\.");
		QueueSink qsink = new QueueSink(1);
		Queue<Object> queue = qsink.getQueue(0);
		Connector.connect(mf, qsink);
		Pushable in = mf.getPushableInput(0);
		in.push("abc|hello.|hi.");
		assertEquals(2, queue.size());
		s = (String) queue.remove();
		assertEquals("|hello.", s);
		s = (String) queue.remove();
		assertEquals("|hi.", s);
	}
	
	@Test
	public void testTokenFeederPush3() 
	{
		String s;
		FindPattern mf = new FindPattern(".*?\n");
		QueueSink qsink = new QueueSink(1);
		Queue<Object> queue = qsink.getQueue(0);
		Connector.connect(mf, qsink);
		Pushable in = mf.getPushableInput(0);
		in.push("hello\nhi\n");
		assertEquals(2, queue.size());
		s = (String) queue.remove();
		assertEquals("hello", s);
		s = (String) queue.remove();
		assertEquals("hi", s);
	}
	
	@Test
	public void testTokenFeederPull1() 
	{
		Object o;
		QueueSource qsource = new QueueSource(1);
		Vector<Object> events = new Vector<Object>();
		events.add("|hello.|hi.");
		qsource.setEvents(events);
		FindPattern mf = new FindPattern("\\|.*?\\.");
		Connector.connect(qsource, mf);
		Pullable p = mf.getPullableOutput(0);
		o = p.pullSoft();
		assertEquals("|hello.", (String) o);
		o = p.pullSoft();
		assertEquals("|hi.", (String) o);
	}
	
	@Test
	public void testPatternCapture1()
	{
		QueueSource qs = new QueueSource();
		qs.setEvents(new Object[]{"abc,d", "e,fgh,"});
		qs.loop(false);
		FindPattern ps  = new FindPattern("(.*?),");
		Connector.connect(qs, ps);
		Pullable p = ps.getPullableOutput();
		assertTrue(p.hasNext());
		assertEquals("abc", p.next());
		assertTrue(p.hasNext());
		assertEquals("de", p.next());
		assertTrue(p.hasNext());
		assertEquals("fgh", p.next());
		assertFalse(p.hasNext());
	}
	
}
