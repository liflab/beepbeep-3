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

import static org.junit.Assert.assertEquals;

import java.io.IOException;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.io.ReadStringStream;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.util.FindPattern;
import ca.uqac.lif.cep.util.Strings;

public class InputTest
{
	@Test
	public void testCsvFeederNoTrim1() throws IOException
	{
		ReadStringStream sr = new ReadStringStream(InputTest.class.getResourceAsStream("resource/test1.csv"));
		FindPattern csv = new FindPattern("(.*?),");
		Connector.connect(sr, csv);
		csv.trim(false);
		QueueSink sink = new QueueSink(1);
		Connector.connect(csv, sink);
		String recv;
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("0", recv);
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("1", recv);
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("2", recv);
	}
	
	@Test
	public void testCsvFeederNoTrim2() throws IOException
	{
		ReadStringStream sr = new ReadStringStream(InputTest.class.getResourceAsStream("resource/test1.csv"));
		FindPattern csv = new FindPattern(".*?,");
		Connector.connect(sr, csv);
		csv.trim(false);
		QueueSink sink = new QueueSink(1);
		Connector.connect(csv, sink);
		String recv;
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("0,", recv);
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("1,", recv);
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("2,", recv);
	}
	
	@Test
	public void testCsvFeederTrim() throws IOException
	{
		ReadStringStream sr = new ReadStringStream(InputTest.class.getResourceAsStream("resource/test2.csv"));
		FindPattern csv = new FindPattern("(.*?),");
		csv.trim(true);
		Connector.connect(sr, csv);
		QueueSink sink = new QueueSink(1);
		Connector.connect(csv, sink);
		String recv;
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("0", recv);
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("1", recv);
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		assertEquals("2", recv);
	}
	
	@Test
	public void testCsvToArrayTrim()
	{
		String line = "a, b, c";
		Strings.SplitString cta = new Strings.SplitString(",");
		cta.trim(true);
		Object[] out = new Object[1];
		cta.evaluate(new Object[]{line}, out);
		Object[] vals = (Object[]) out[0];
		assertEquals(3, vals.length);
		assertEquals("a", vals[0]);
		assertEquals("b", vals[1]);
		assertEquals("c", vals[2]);		
	}
	
	@Test
	public void testCsvToArrayNoTrim()
	{
		String line = "a, b, c";
		Strings.SplitString cta = new Strings.SplitString(",");
		cta.trim(false);
		Object[] out = new Object[1];
		cta.evaluate(new Object[]{line}, out);
		Object[] vals = (Object[]) out[0];
		assertEquals(3, vals.length);
		assertEquals("a", vals[0]);
		assertEquals(" b", vals[1]);
		assertEquals(" c", vals[2]);		
	}
	
	@Test
	public void testCsvToArrayNumber()
	{
		String line = "a, 32, 2.5";
		Strings.SplitString cta = new Strings.SplitString(",");
		cta.trim(true);
		Object[] out = new Object[1];
		cta.evaluate(new Object[]{line}, out);
		Object[] vals = (Object[]) out[0];
		assertEquals(3, vals.length);
		assertEquals("a", vals[0]);
		assertEquals(32, vals[1]);
		assertEquals(2.5f, vals[2]);		
	}
}
