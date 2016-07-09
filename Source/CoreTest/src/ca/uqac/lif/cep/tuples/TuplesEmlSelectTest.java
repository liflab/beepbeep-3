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

import java.io.InputStream;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.CumulativeProcessor;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.epl.CountDecimate;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.interpreter.InterpreterTestFrontEnd;
import ca.uqac.lif.cep.io.StreamGrammar;
import ca.uqac.lif.cep.io.StreamReader;
import ca.uqac.lif.cep.numbers.NumberGrammar;
import ca.uqac.lif.cep.tuples.NamedTuple;
import ca.uqac.lif.cep.tuples.Select;
import ca.uqac.lif.cep.tuples.TupleFeeder;
import ca.uqac.lif.cep.tuples.TupleGrammar;
import ca.uqac.lif.cep.util.StringUtils;
import ca.uqac.lif.util.PackageFileReader;

public class TuplesEmlSelectTest
{
	protected InterpreterTestFrontEnd m_interpreter;

	@Before
	public void setUp()
	{
		m_interpreter = new InterpreterTestFrontEnd();
		m_interpreter.extendGrammar(NumberGrammar.class);
		m_interpreter.extendGrammar(StreamGrammar.class);
		m_interpreter.extendGrammar(TupleGrammar.class);
	}
	
	@Test
	public void testSelect1() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT 0 FROM (0)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof Number);
		Number n = (Number) answer;
		assertEquals(0, n.intValue());
	}
	
	@Test
	public void testSelect2() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT z FROM (0)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof Number);
		Number n = (Number) answer;
		assertEquals(0, n.intValue());
	}
	
	@Test
	public void testSelect3() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT t.z FROM (0 AS t)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof Number);
		Number n = (Number) answer;
		assertEquals(0, n.intValue());
	}
	
	@Test
	public void testSelect4() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT u.z FROM (1 AS t, 2 AS u)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof Number);
		Number n = (Number) answer;
		assertEquals(2, n.intValue());
	}
	
	@Test
	public void testSelect5() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT (u.z) + (t.z) FROM (1 AS t, 2 AS u)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof Number);
		Number n = (Number) answer;
		assertEquals(3, n.intValue());
	}
	
	@Test
	public void testSelect6() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT u.z AS w FROM (01 AS t, 2 AS u)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof NamedTuple);
		NamedTuple tup = (NamedTuple) answer;
		assertEquals(1, tup.keySet().size());
		assertEquals(2, ((Number) tup.get("w")).intValue());
	}
	
	@Test
	public void testSelect7() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT u.z AS w, (t.z) + (3) AS v FROM (1 AS t, 2 AS u)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof NamedTuple);
		NamedTuple tup = (NamedTuple) answer;
		assertEquals(2, tup.keySet().size());
		assertEquals(4, ((Number) tup.get("v")).intValue());
	}
	
	@Test
	public void testSelect8() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT a AS a, (b) + (3) AS n FROM (1)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		{
			// We unplug the constant trace "1" and replace it by the token feeder
			// as input for the SELECT statement
			String file_contents = PackageFileReader.readPackageFile(this.getClass(), "resource/tuples1.csv");
			InputStream stream = StringUtils.toInputStream(file_contents);
			StreamReader sr = new StreamReader(stream);
			TupleFeeder tf = new TupleFeeder();
			Connector.connect(sr, tf);
			Connector.connect(tf, s);
		}
		Pullable p = s.getPullableOutput(0);
		{
			// Get first tuple
			Object answer = p.pull();
			assertTrue(answer instanceof NamedTuple);
			NamedTuple tup = (NamedTuple) answer;
			assertEquals(2, tup.keySet().size());
			assertEquals(0, ((Number) tup.get("a")).intValue());
			assertEquals(3, ((Number) tup.get("n")).intValue());
		}
		{
			// Get next tuple
			Object answer = p.pull();
			assertTrue(answer instanceof NamedTuple);
			NamedTuple tup = (NamedTuple) answer;
			assertEquals(2, tup.keySet().size());
			assertEquals(1, ((Number) tup.get("a")).intValue());
			assertEquals(3, ((Number) tup.get("n")).intValue());
		}
	}
	
	@Test
	public void testSelect9() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT (t.a) + (u.b) AS x, (u.c) + (3) AS y FROM (1 AS t, 0 AS u)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		{
			// We unplug the constant trace t and replace it by the token feeder
			// as input for the SELECT statement
			String file_contents = PackageFileReader.readPackageFile(this.getClass(), "resource/tuples1.csv");
			InputStream stream = StringUtils.toInputStream(file_contents);
			StreamReader sr = new StreamReader(stream);
			TupleFeeder tf = new TupleFeeder();
			Connector.connect(sr, tf);
			Connector.connect(tf, s, 0, 0);
		}
		{
			// Ditto for the constant trace u
			String file_contents = PackageFileReader.readPackageFile(this.getClass(), "resource/tuples2.csv");
			InputStream stream = StringUtils.toInputStream(file_contents);
			StreamReader sr = new StreamReader(stream);
			TupleFeeder tf = new TupleFeeder();
			Connector.connect(sr, tf);
			Connector.connect(tf, s, 0, 1);
		}
		Pullable p = s.getPullableOutput(0);
		{
			// Get first tuple
			Object answer = p.pull();
			assertTrue(answer instanceof NamedTuple);
			NamedTuple tup = (NamedTuple) answer;
			assertEquals(2, tup.keySet().size());
			assertEquals(2, ((Number) tup.get("x")).intValue());
			assertEquals(6, ((Number) tup.get("y")).intValue());
		}
		{
			// Get next tuple
			Object answer = p.pull();
			assertTrue(answer instanceof NamedTuple);
			NamedTuple tup = (NamedTuple) answer;
			assertEquals(2, tup.keySet().size());
			assertEquals(5, ((Number) tup.get("x")).intValue());
			assertEquals(9, ((Number) tup.get("y")).intValue());
		}
		{
			// Get next tuple
			Object answer = p.pull();
			assertTrue(answer instanceof NamedTuple);
			NamedTuple tup = (NamedTuple) answer;
			assertEquals(2, tup.keySet().size());
			assertEquals(8, ((Number) tup.get("x")).intValue());
			assertEquals(12, ((Number) tup.get("y")).intValue());
		}
	}
	
	@Test
	public void testSelect10() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("SELECT SIN(x) FROM (1)");
		assertTrue(processor instanceof Select);
		Select s = (Select) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof Number);
		Number n = (Number) answer;
		assertEquals(Math.sin(1), n.floatValue(), 0.01);
	}
	
	@Test
	public void testCombine1() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("COMBINE (1) WITH ADDITION");
		assertNotNull(processor);
		assertTrue(processor instanceof CumulativeProcessor);
		CumulativeProcessor s = (CumulativeProcessor) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof Number);
		Number num = (Number) answer;
		assertEquals(1, num.intValue());
		num = (Number) p.pull();
		assertEquals(2, num.intValue());
		num = (Number) p.pull();
		assertEquals(3, num.intValue());
	}
	
	@Test
	public void testCombine2() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("COMBINE (2) WITH MULTIPLICATION");
		assertTrue(processor instanceof CumulativeProcessor);
		CumulativeProcessor s = (CumulativeProcessor) processor;
		Pullable p = s.getPullableOutput(0);
		Object answer = p.pull();
		assertTrue(answer instanceof Number);
		Number num = (Number) answer;
		assertEquals(2, num.intValue());
		num = (Number) p.pull();
		assertEquals(4, num.intValue());
		num = (Number) p.pull();
		assertEquals(8, num.intValue());
	}

	
	@Test
	public void testSelectMixed1() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("EVERY 2ND OF (SELECT (t.a) + (u.b) AS x, (u.c) + (3) AS y FROM (THE TUPLES OF FILE \"tuples1.csv\" AS t, THE TUPLES OF FILE \"tuples2.csv\" AS u))");
		assertTrue(processor instanceof CountDecimate);
		CountDecimate cd = (CountDecimate) processor;
		Pullable p = cd.getPullableOutput(0);
		{
			// Get first tuple
			Object answer = p.pullHard();
			assertTrue(answer instanceof NamedTuple);
			NamedTuple tup = (NamedTuple) answer;
			assertEquals(2, tup.keySet().size());
			assertEquals(2, ((Number) tup.get("x")).intValue());
			assertEquals(6, ((Number) tup.get("y")).intValue());
		}
		{
			// Get next tuple
			Object answer = p.pullHard();
			assertTrue(answer instanceof NamedTuple);
			NamedTuple tup = (NamedTuple) answer;
			assertEquals(2, tup.keySet().size());
			assertEquals(8, ((Number) tup.get("x")).intValue());
			assertEquals(12, ((Number) tup.get("y")).intValue());
		}
		{
			// Get next tuple. There is no next tuple
			Object answer = p.pull();
			assertNull(answer);
		}
	}

	@Test
	public void testTupleFeeder1() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("THE TUPLES OF FILE \"tuples1.csv\"");
		assertTrue(processor instanceof TupleFeeder);
		QueueSink sink = new QueueSink(1);
		Connector.connect((Processor) processor, sink);
		NamedTuple recv;
		// First tuple
		sink.pullHard();
		recv = (NamedTuple) sink.getQueue(0).remove();
		assertNotNull(recv);
		assertEquals(0, ((Number) recv.get("a")).intValue());
		assertEquals(0, ((Number) recv.get("b")).intValue());
		assertEquals(0, ((Number) recv.get("c")).intValue());
		// Another tuple
		sink.pullHard();
		recv = (NamedTuple) sink.getQueue(0).remove();
		assertNotNull(recv);
		assertEquals(1, ((Number) recv.get("a")).intValue());
		assertEquals(0, ((Number) recv.get("b")).intValue());
		assertEquals(1, ((Number) recv.get("c")).intValue());
		// Another tuple
		sink.pullHard();
		recv = (NamedTuple) sink.getQueue(0).remove();
		assertNotNull(recv);
		assertEquals(2, ((Number) recv.get("a")).intValue());
		assertEquals(4, ((Number) recv.get("b")).intValue());
		assertEquals(5, ((Number) recv.get("c")).intValue());		
	}
	
	@Test
	public void testTupleFeeder2()
	{
		String file_contents = PackageFileReader.readPackageFile(this.getClass(), "resource/tuples1.csv");
		InputStream stream = StringUtils.toInputStream(file_contents);
		StreamReader sr = new StreamReader(stream);
		TupleFeeder csv = new TupleFeeder();
		Connector.connect(sr, csv);
		QueueSink sink = new QueueSink(1);
		Connector.connect(csv, sink);
		NamedTuple recv;
		// First tuple
		sink.pullHard();
		recv = (NamedTuple) sink.getQueue(0).remove();
		assertNotNull(recv);
		assertEquals(0, ((Number) recv.get("a")).intValue());
		assertEquals(0, ((Number) recv.get("b")).intValue());
		assertEquals(0, ((Number) recv.get("c")).intValue());
		// Another tuple
		sink.pullHard();
		recv = (NamedTuple) sink.getQueue(0).remove();
		assertNotNull(recv);
		assertEquals(1, ((Number) recv.get("a")).intValue());
		assertEquals(0, ((Number) recv.get("b")).intValue());
		assertEquals(1, ((Number) recv.get("c")).intValue());
		// Another tuple
		sink.pullHard();
		recv = (NamedTuple) sink.getQueue(0).remove();
		assertNotNull(recv);
		assertEquals(2, ((Number) recv.get("a")).intValue());
		assertEquals(4, ((Number) recv.get("b")).intValue());
		assertEquals(5, ((Number) recv.get("c")).intValue());		
	}
	
	@Test
	public void testWhere1() throws ParseException
	{
		Object processor = m_interpreter.parseQuery("(THE TUPLES OF FILE \"tuples1.csv\") WHERE (a) = (0)");
		assertTrue(processor instanceof Processor);
		Processor p = (Processor) processor;
		Pullable pul = p.getPullableOutput(0);
		NamedTuple recv;
		// First tuple
		recv = (NamedTuple) pul.pullHard();
		assertNotNull(recv);
		assertEquals(0, ((Number) recv.get("a")).intValue());
		assertEquals(0, ((Number) recv.get("b")).intValue());
		assertEquals(0, ((Number) recv.get("c")).intValue());
		// Other tuple
		recv = (NamedTuple) pul.pullHard();
		assertNotNull(recv);
		assertEquals(0, ((Number) recv.get("a")).intValue());
		assertEquals(1, ((Number) recv.get("b")).intValue());
		assertEquals(6, ((Number) recv.get("c")).intValue());
		
	}


}
