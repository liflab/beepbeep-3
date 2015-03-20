package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import java.util.Queue;

import org.junit.Before;
import org.junit.Test;

public class ProcessorTest
{

	@Before
	public void setUp() throws Exception
	{
		// Nothing to do
	}
	
	@Test
	public void testPush1()
	{
		QueueSource cp = new QueueSource("A", 1);
		QueueSink qs = new QueueSink(1);
		Connector.connect(cp, qs);
		cp.push();
		if (qs.getQueue(0).size() != 1)
		{
			fail("Expected one event in sink queue");
		}
		cp.push();
		if (qs.getQueue(0).size() != 2)
		{
			fail("Expected two events in sink queue");
		}
	}
	
	@Test
	public void testSumPush()
	{
		QueueSource cp = new QueueSource(1, 1);
		Sum cs = new Sum(1);
		QueueSink qs = new QueueSink(1);
		Connector.connect(cp, cs);
		Connector.connect(cs, qs);
		Queue<Object> q = qs.getQueue(0);
		Number n;
		cp.push();
		n = (Number) q.remove();
		if (n.intValue() != 1)
		{
			fail("Wrong number");
		}
		cp.push();
		n = (Number) q.remove();
		if (n.intValue() != 2)
		{
			fail("Wrong number");
		}
		cp.push();
		n = (Number) q.remove();
		if (n.intValue() != 3)
		{
			fail("Wrong number");
		}
	}
	
	@Test
	public void testSumPull()
	{
		QueueSource cp = new QueueSource(1, 1);
		Sum cs = new Sum(1);
		QueueSink qs = new QueueSink(1);
		Connector.connect(cp, cs);
		Connector.connect(cs, qs);
		Queue<Object> q = qs.getQueue(0);
		Number n;
		qs.pull();
		n = (Number) q.remove();
		if (n.intValue() != 1)
		{
			fail("Wrong number");
		}
		qs.pull();
		n = (Number) q.remove();
		if (n.intValue() != 2)
		{
			fail("Wrong number");
		}
		qs.pull();
		n = (Number) q.remove();
		if (n.intValue() != 3)
		{
			fail("Wrong number");
		}
	}

	@Test
	public void testPull1()
	{
		QueueSource cp = new QueueSource("A", 1);
		String recv;
		Pullable p = cp.getPullableOutput(0);
		recv = (String) p.pull();
		if (recv == null)
		{
			fail("Expected a string, got null");
		}
		if (recv.compareTo("A") != 0)
		{
			fail("Expected 'A', got something else");
		}
	}

}
