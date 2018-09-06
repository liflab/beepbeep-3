package ca.uqac.lif.cep.functions;

import static org.junit.Assert.*;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.util.Booleans;

public class ApplyFunctionLazyTest 
{
	@Test
	public void test1()
	{
		Function f = Booleans.and;
		ApplyFunctionPartial afl = new ApplyFunctionPartial(f);
		Pushable p1 = afl.getPushableInput(0);
		Pushable p2 = afl.getPushableInput(1);
		QueueSink qs = new QueueSink();
		Connector.connect(afl, qs);
		Queue<Object> queue = qs.getQueue();
		p1.push(false);
		assertFalse(queue.isEmpty());
		Boolean b = (Boolean) queue.remove();
		assertEquals(false, b);
		p1.push(true);
		assertTrue(queue.isEmpty());
		p2.push(false);
		assertTrue(queue.isEmpty());
		p2.push(true);
		assertFalse(queue.isEmpty());
		b = (Boolean) queue.remove();
		assertEquals(true, b);
	}
}
