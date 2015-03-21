package ca.uqac.lif.cep.input;

import static org.junit.Assert.*;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.QueueSink;
import ca.uqac.lif.cep.io.StreamReader;

public class InputTest
{

	@Before
	public void setUp() throws Exception
	{
	}

	@Test
	public void testCsvFeeder() throws IOException
	{
		StreamReader sr = new StreamReader(new FileInputStream(new File("src/ca/uqac/lif/cep/input/resource/test1.csv")));
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
			fail("Expected " + expected + ", got " + recv);
		}
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		expected = "1";
		if (recv == null || recv.compareTo(expected) != 0)
		{
			fail("Expected " + expected + ", got " + recv);
		}
		sink.pullHard();
		recv = (String) sink.getQueue(0).remove();
		expected = "2";
		if (recv == null || recv.compareTo(expected) != 0)
		{
			fail("Expected " + expected + ", got " + recv);
		}
	}

}
