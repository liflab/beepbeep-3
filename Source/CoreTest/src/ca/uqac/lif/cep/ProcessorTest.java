package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import java.util.LinkedList;
import java.util.Queue;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.math.Addition;

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
			fail("Expected 'A', got " + recv);
		}
	}
	
	@Test
	public void testWindowPull1()
	{
		Number recv;
		QueueSource cs = new QueueSource(1, 1); // Sequence of 1s
		Window wp = new Window(new Sum(1), 3);
		Connector.connect(cs, wp);
		Pullable p = wp.getPullableOutput(0);
		// We must pull three times to get the first output
		recv = (Number) p.pull();
		if (recv != null)
		{
			fail("Expected null on first pull, got " + recv);
		}
		recv = (Number) p.pull();
		if (recv != null)
		{
			fail("Expected null on second pull, got " + recv);
		}
		recv = (Number) p.pull();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on third pull, got " + recv);
		}
		recv = (Number) p.pull();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on fourth pull, got " + recv);
		}
	}
	
	@Test
	public void testWindowPush1()
	{
		Number recv;
		QueueSource cs = new QueueSource(1, 1); // Sequence of 1s
		Window wp = new Window(new Sum(1), 3);
		QueueSink qs = new QueueSink(1);
		Connector.connect(cs, wp);
		Connector.connect(wp, qs);
		// We must push three times to get the first output
		cs.push();
		recv = (Number) qs.remove().elementAt(0);
		if (recv != null)
		{
			fail("Expected null on first push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove().elementAt(0);
		if (recv != null)
		{
			fail("Expected null on second push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove().elementAt(0);
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on third push, got " + recv);
		}
		cs.push();
		recv = (Number) qs.remove().elementAt(0);
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on fourth push, got " + recv);
		}
	}
	
	@Test
	public void testDecimatePull1()
	{
		int op_num = 0;
		QueueSource ones = new QueueSource(1, 1);
		Sum count = new Sum(1);
		Connector.connect(ones, count);
		CountDecimate decim = new CountDecimate(2);
		Connector.connect(count, decim);
		QueueSink sink = new QueueSink(1);
		Connector.connect(decim, sink);
		Number recv;
		sink.pull();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1 on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv != null)
		{
			fail("Expected null on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv != null)
		{
			fail("Expected null on pull " + op_num + ", got " + recv);
		}
		sink.pull();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv == null || recv.intValue() != 5)
		{
			fail("Expected 5 on pull " + op_num + ", got " + recv);
		}
	}
	
	@Test
	public void testDecimatePush1()
	{
		int op_num = 0;
		QueueSource ones = new QueueSource(1, 1);
		Sum count = new Sum(1);
		Connector.connect(ones, count);
		CountDecimate decim = new CountDecimate(2);
		Connector.connect(count, decim);
		QueueSink sink = new QueueSink(1);
		Connector.connect(decim, sink);
		Number recv;
		ones.push();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1 on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv != null)
		{
			fail("Expected null on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3 on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv != null)
		{
			fail("Expected null on push " + op_num + ", got " + recv);
		}
		ones.push();
		op_num++;
		recv = (Number) sink.remove().firstElement();
		if (recv == null || recv.intValue() != 5)
		{
			fail("Expected 5 on push " + op_num + ", got " + recv);
		}
	}
	
	@Test
	public void testAdditionPush1()
	{
		LinkedList<Object> l_input1 = new LinkedList<Object>();
		l_input1.add(1);
		l_input1.add(2);
		l_input1.add(3);
		LinkedList<Object> l_input2 = new LinkedList<Object>();
		l_input2.add(6);
		l_input2.add(4);
		l_input2.add(0);
		QueueSource input1 = new QueueSource(l_input1, 1);
		QueueSource input2 = new QueueSource(l_input2, 1);
		Function add = new Function(new Addition(2));
		Connector.connect(input1, input2, add);
		QueueSink sink = new QueueSink(1);
		Connector.connect(add, sink);
		Number recv;
		input1.push();
		input2.push();
		recv = (Number) sink.remove().firstElement(); // 1 + 6
		if (recv == null || recv.intValue() != 7)
		{
			fail("Expected 7, got " + recv);
		}
		input1.push(); // We only push on first input
		recv = (Number) sink.remove().firstElement(); // 2 + ?
		if (recv != null)
		{
			// Can't compute an output event; we're waiting for right input
			fail("Expected null, got " + recv);
		}
		input1.push();
		input2.push();
		recv = (Number) sink.remove().firstElement(); // 2 + 4
		if (recv == null || recv.intValue() != 6)
		{
			fail("Expected 10, got " + recv);
		}
		input2.push();
		// Only need to push on right; left already in queue
		recv = (Number) sink.remove().firstElement(); // 3 + 0
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3, got " + recv);
		}
	}
	
	@Test
	public void testFilter1()
	{
		LinkedList<Object> l_input1 = new LinkedList<Object>();
		l_input1.add(1);
		l_input1.add(2);
		l_input1.add(3);
		l_input1.add(4);
		LinkedList<Object> l_input2 = new LinkedList<Object>();
		l_input2.add(true);
		l_input2.add(false);
		l_input2.add(true);
		l_input2.add(false);
		QueueSource input1 = new QueueSource(l_input1, 1);
		QueueSource input2 = new QueueSource(l_input2, 1);
		Filter f = new Filter();
		Connector.connect(input1, input2, f);
		QueueSink sink = new QueueSink(1);
		Connector.connect(f, sink);
		Number recv;
		input1.push();
		input2.push();
		recv = (Number) sink.remove().firstElement(); // 1
		if (recv == null || recv.intValue() != 1)
		{
			fail("Expected 1, got " + recv);
		}
		input1.push();
		input2.push();
		recv = (Number) sink.remove().firstElement(); // null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}
		input1.push();
		input1.push();
		input2.push();
		recv = (Number) sink.remove().firstElement(); // 1
		if (recv == null || recv.intValue() != 3)
		{
			fail("Expected 3, got " + recv);
		}
		input1.push();
		input2.push();
		recv = (Number) sink.remove().firstElement(); // null
		if (recv != null)
		{
			fail("Expected null, got " + recv);
		}
		
	}

}
