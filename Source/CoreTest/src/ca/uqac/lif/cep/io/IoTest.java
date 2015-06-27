package ca.uqac.lif.cep.io;

import static org.junit.Assert.*;

import java.io.FileNotFoundException;
import java.io.InputStream;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.QueueSink;
import ca.uqac.lif.util.PackageFileReader;
import ca.uqac.lif.util.StringUtils;

public class IoTest
{

	@Before
	public void setUp() throws Exception
	{
	}
	
	@Test
	public void testStreamReaderPush1() throws FileNotFoundException
	{
		String file_contents = PackageFileReader.readPackageFile(this.getClass(), "resource/test1.txt");
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
	
}
