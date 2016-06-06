package ca.uqac.lif.cep;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.epl.QueueSink;

/**
 * Unit tests for the {@link Connector} class
 * @author Sylvain Hallé
 */
public class ConnectorTest 
{
	@Test
	public void testTwoUnary()
	{
		Passthrough p1 = new Passthrough(1);
		QueueSink qs1 = new QueueSink(1);
		Connector.connect(p1, qs1);
		Pushable push1 = p1.getPushableInput(0);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qs1.getQueue(0);
			for (int i = 0; i < 5; i++)
			{
				push1.push(i);
				Utilities.queueContains(i, queue);
			}
			p1.reset();
			qs1.reset();
		}
	}
	
	@Test
	public void testTwoBinary()
	{
		Passthrough p1 = new Passthrough(2);
		QueueSink qs1 = new QueueSink(2);
		Connector.connect(p1, qs1, 0, 1);
		Connector.connect(p1, qs1, 1, 0);
		Pushable push1 = p1.getPushableInput(0);
		Pushable push2 = p1.getPushableInput(1);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue1 = qs1.getQueue(0);
			Queue<Object> queue2 = qs1.getQueue(1);
			for (int i = 0; i < 5; i++)
			{
				push1.push(i);
				push2.push(2 * i + 1);
				Utilities.queueContains(i, queue2);
				Utilities.queueContains(2 * i + 1, queue1);
			}
			p1.reset();
			qs1.reset();
		}
	}
	
	@Test
	public void testThreeUnary()
	{
		Passthrough p1 = new Passthrough(1);
		Passthrough p2 = new Passthrough(1);
		QueueSink qs1 = new QueueSink(1);
		Connector.connect(p1, p2, qs1);
		Pushable push1 = p1.getPushableInput(0);
		for (int k = 0; k < 2; k++)
		{
			Queue<Object> queue = qs1.getQueue(0);
			for (int i = 0; i < 5; i++)
			{
				push1.push(i);
				Utilities.queueContains(i, queue);
			}
			p1.reset();
			qs1.reset();
		}
	}
}
