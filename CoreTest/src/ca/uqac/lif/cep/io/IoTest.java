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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.InputStream;

import org.junit.Test;

import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.NextStatus;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.util.FileHelper;
import ca.uqac.lif.cep.util.StringUtils;

/**
 * Unit tests for input-output processors
 * @author Sylvain Hallé
 */
public class IoTest extends BeepBeepUnitTest
{	
	@Test
	public void testStreamReaderPush1() throws FileNotFoundException, ConnectorException
	{
		String file_contents = FileHelper.internalFileToString(this.getClass(), "resource/test1.txt");
		InputStream stream = StringUtils.toInputStream(file_contents);
		StreamReader sr = new StreamReader(stream);
		QueueSink sink = new QueueSink(1);
		Connector.connect(sr, sink);
		sr.push();
		String recv = (String) sink.getQueue(0).remove();
		assertNotNull(recv);
		recv = recv.trim();
		assertEquals(35, recv.length());
	}
	
	@Test
	public void testStreamReaderPull1() throws FileNotFoundException, ConnectorException
	{
		String file_contents = FileHelper.internalFileToString(this.getClass(), "resource/test1.txt");
		InputStream stream = StringUtils.toInputStream(file_contents);
		StreamReader sr = new StreamReader(stream);
		sr.setIsFile(true);
		int turns = 0;
		Pullable p = sr.getPullableOutput(0);
		@SuppressWarnings("unused")
		String s = "";
		while (p.hasNextSoft() != NextStatus.NO)
		{
			turns++;
			String pulled = (String) p.pullSoft();
			assertNotNull(pulled);
			s += p.pullSoft();
		}
		assertTrue("Pulled the source for too long", turns < 4);
	}
	
	@Test
	public void testUrlFeeder1() throws ConnectorException
	{
		HttpReader hr = new HttpReader("https://raw.githubusercontent.com/liflab/beepbeep-3/master/CoreTest/tuples1.csv");
		Pullable p = hr.getPullableOutput(0);
		assertNotNull(p);
		Object o = p.pullSoft();
		assertTrue(o instanceof String);
	}
	
}
