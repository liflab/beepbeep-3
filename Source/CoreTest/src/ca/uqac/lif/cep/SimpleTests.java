package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.epl.QueueSink;

/**
 * Unit tests for a few simple processors: {@link Constant}, 
 * {@link Passthrough}
 * @author Sylvain Hallé
 */
public class SimpleTests
{
	@Test
	public void testConstant()
	{
		String out = null;
		Constant c = new Constant("A");
		TypedPullable<String> p = new TypedPullable<String>(c.getPullableOutput(0));
		out = p.pull();
		assertEquals("A", out);
		out = p.pull();
		assertEquals("A", out);
	}
	
	@Test
	public void testPassthrough()
	{
		Passthrough c = new Passthrough(1);
		QueueSink sink = new QueueSink(1);
		Connector.connect(c,  sink);
		Pushable in = c.getPushableInput(0);
		Queue<Object> q = sink.getQueue(0);
		for (int i = 0; i < 10; i++)
		{
			in.push(i);
			int out = (int) q.remove();
			assertEquals(i, out);
		}
	}
}
