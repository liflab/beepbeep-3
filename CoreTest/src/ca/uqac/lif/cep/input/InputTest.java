package ca.uqac.lif.cep.input;

import static org.junit.Assert.assertEquals;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.junit.Test;

import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.io.StringStreamReader;
import ca.uqac.lif.cep.tmf.QueueSink;

public class InputTest extends BeepBeepUnitTest
{
	@Test
	public void testCsvFeeder() throws IOException
	{
		StringStreamReader sr = new StringStreamReader(InputTest.class.getResourceAsStream("resource/test1.csv"));
		CsvFeeder csv = new CsvFeeder();
		Connector.connect(sr, csv);
		QueueSink sink = new QueueSink(1);
		Connector.connect(csv, sink);
		String recv, expected;
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		expected = "0";
		if (recv == null || recv.compareTo(expected) != 0)
		{
			assertEquals(expected, recv);
		}
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		expected = "1";
		if (recv == null || recv.compareTo(expected) != 0)
		{
			assertEquals(expected, recv);
		}
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		expected = "2";
		if (recv == null || recv.compareTo(expected) != 0)
		{
			assertEquals(expected, recv);
		}
	}
	
	/**
	 * Converts a string into an input stream
	 * @param s The string to read from
	 * @return The input stream with the contents of the string
	 */
	public static InputStream toInputStream(String s)
	{
		return new ByteArrayInputStream(s.getBytes());
	}

}
