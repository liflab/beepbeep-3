package ca.uqac.lif.cep.io;

import static org.junit.Assert.*;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.QueueSink;

public class IoTest
{

	@Before
	public void setUp() throws Exception
	{
	}
	
	@Test
	public void testStreamReaderPush1() throws FileNotFoundException
	{
		StreamReader sr = new StreamReader(new FileInputStream(new File("src/ca/uqac/lif/cep/io/resource/test1.txt")));
		QueueSink sink = new QueueSink(1);
		Connector.connect(sr, sink);
		sr.push();
		String recv = (String) sink.getQueue(0).remove();
		if (recv == null)
		{
			fail("Expected string, got null");
		}
		recv = recv.trim();
		int len = recv.length();
		if (len != 35)
		{
			fail("String has wrong length (" + len + ")");
		}
	}
	
}
