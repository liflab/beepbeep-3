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
package ca.uqac.lif.cep.io;

import static org.junit.Assert.*;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;

import org.junit.Assume;
import org.junit.Test;

import ca.uqac.lif.cep.NextStatus;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.PullableException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Pushable.PushableException;
import ca.uqac.lif.cep.util.FileHelper;

/**
 * Unit tests for input-output processors
 * @author Sylvain Hallé
 */
public class IoTest
{
	/**
	 * A variable that checks if the computer has an internet connection.
	 * There is no point in running (and failing) some of the tests on a
	 * computer that is offline. Set this to false to run tests in such a
	 * situation.
	 */
	protected static boolean s_hasConnection = true;
	
	@Test
	public void testStreamReaderFile()
	{
		String s;
		InputStream is = IoTest.class.getResourceAsStream("resource/test1.txt");
		ReadStringStream bsr = new ReadStringStream(is);
		// Set tiny chunk sizes to simulate reading large files
		bsr.setChunkSize(10);
		bsr.setIsFile(true);
		Pullable p = bsr.getPullableOutput();
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("A simple t", s);
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("ext file w", s);
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("ith short ", s);
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("text.", s);
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testStreamReaderNoFile()
	{
		String s;
		InputStream is = IoTest.class.getResourceAsStream("resource/test1.txt");
		ReadStringStream bsr = new ReadStringStream(is);
		// Set tiny chunk sizes to simulate reading large files
		bsr.setChunkSize(10);
		bsr.setIsFile(false);
		Pullable p = bsr.getPullableOutput();
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("A simple t", s);
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("ext file w", s);
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("ith short ", s);
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("text.", s);
		assertEquals(NextStatus.MAYBE, p.hasNextSoft());
	}
	
	@Test
	public void testStreamReaderEot()
	{
		String s;
		StringBuilder content = new StringBuilder();
		content.append("01234567890123").append(ReadInputStream.END_CHARACTER);
		ByteArrayInputStream bais = new ByteArrayInputStream(content.toString().getBytes());
		ReadStringStream bsr = new ReadStringStream(bais);
		// Set tiny chunk sizes to simulate reading large files
		bsr.setChunkSize(10);
		bsr.setIsFile(false);
		Pullable p = bsr.getPullableOutput();
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("0123456789", s);
		assertTrue(p.hasNext());
		s = (String) p.next();
		assertEquals("0123", s);
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testUrlFeeder1() 
	{
		Assume.assumeTrue(s_hasConnection);
		HttpGet hr = new HttpGet("https://raw.githubusercontent.com/liflab/beepbeep-3/master/CoreTest/tuples1.csv");
		Pullable p = hr.getPullableOutput(0);
		assertNotNull(p);
		Object o = p.pullSoft();
		assertTrue(o instanceof String);
	}
	
	@Test(expected=PullableException.class)
	public void testUrlFeeder2() 
	{
		// Malformed URL
		HttpGet hr = new HttpGet("https://0.0.0.0.0.0");
		Pullable p = hr.getPullableOutput(0);
		assertNotNull(p);
		p.pullSoft();
	}
	
	@Test
	public void testPrint()
	{
		String s;
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		Print print = new Print(new PrintStream(baos));
		print.setSeparator(",");
		print.setPrefix("A");
		print.setSuffix("B");
		Pushable p = print.getPushableInput();
		p.push("foo");
		s = new String(baos.toByteArray());
		assertEquals("AfooB,", s);
		p.push("bar");
		s = new String(baos.toByteArray());
		assertEquals("AfooB,AbarB,", s);
	}
	
	@Test
	public void testPrettyPrint()
	{
		String s;
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(baos);
		Print print = new Print();
		print.setSeparator(" ");
		print.setPrintStream(ps);
		assertTrue(ps == print.getPrintStream());
		Pushable p = print.getPushableInput();
		p.push(3.5f);
		s = new String(baos.toByteArray());
		assertEquals("3.5 ", s);
		p.push(3f);
		s = new String(baos.toByteArray());
		assertEquals("3.5 3 ", s);
	}
	
	@Test
	public void testPrintException1() throws IOException
	{
		// The print processor does not throw an exception, even
		// if the underlying output stream throws one
		ExceptionOutputStream baos = new ExceptionOutputStream();
		Print print = new Print(new PrintStream(baos));
		Pushable p = print.getPushableInput();
		p.push("bar");
	}
	
	@Test
	public void testLineReader()
	{
		InputStream is = FileHelper.internalFileToStream(IoTest.class, "resource/test2.txt");
		ReadLines lr = new ReadLines(is);
		lr.trim(true);
		Pullable p = lr.getPullableOutput();
		assertEquals("foo", (String) p.pull());
		assertEquals("bar", (String) p.pull());
		assertEquals("baz", (String) p.pull());
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testLineReaderCrlf()
	{
		InputStream is = FileHelper.internalFileToStream(IoTest.class, "resource/test2.txt");
		ReadLines lr = new ReadLines(is);
		lr.addCrlf(true);
		Pullable p = lr.getPullableOutput();
		assertEquals("foo" + ReadLines.CRLF, (String) p.pull());
		assertEquals("bar" + ReadLines.CRLF, (String) p.pull());
		assertEquals("baz" + ReadLines.CRLF, (String) p.pull());
		assertFalse(p.hasNext());
	}
	
	@Test
	public void testOutputStreamProcessor1() throws IOException
	{
		String s;
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		WriteOutputStream osp = new WriteOutputStream(baos);
		Pushable p = osp.getPushableInput();
		p.push("foo");
		s = new String(baos.toByteArray());
		assertEquals("foo", s);
		p.push("bar");
		s = new String(baos.toByteArray());
		assertEquals("foobar", s);
		baos.close();
	}
	
	@Test
	public void testOutputStreamProcessor2() throws IOException
	{
		byte[] s;
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		WriteOutputStream osp = new WriteOutputStream(baos);
		Pushable p = osp.getPushableInput();
		p.push(new byte[]{60, 51, 60});
		s = baos.toByteArray();
		assertEquals(60, s[0]);
		assertEquals(51, s[1]);
		assertEquals(60, s[2]);
		p.push(new byte[]{32, 30, 31});
		s = baos.toByteArray();
		assertEquals(32, s[3]);
		assertEquals(30, s[4]);
		assertEquals(31, s[5]);
		baos.close();
	}
	
	@Test(expected=PushableException.class)
	public void testOutputStreamProcessorException1() throws IOException
	{
		ExceptionOutputStream baos = new ExceptionOutputStream();
		WriteOutputStream osp = new WriteOutputStream(baos);
		Pushable p = osp.getPushableInput();
		p.push("bar");
	}
	
	@Test(expected=PushableException.class)
	public void testOutputStreamProcessorException2() throws IOException
	{
		ExceptionOutputStream baos = new ExceptionOutputStream();
		WriteOutputStream osp = new WriteOutputStream(baos);
		Pushable p = osp.getPushableInput();
		p.push(new Object());
	}
	
	/**
	 * Dummy class to throw an exception
	 */
	protected static class ExceptionOutputStream extends OutputStream
	{
		@Override
		public void write(int b) throws IOException
		{
			throw new IOException();
			
		}
		
	}
	
}
