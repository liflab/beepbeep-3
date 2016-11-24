package ca.uqac.lif.cep.concurrency;

import static org.junit.Assert.*;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.tmf.QueueSource;

public class PullPipelineTest 
{
	@Test
	public void test1() throws ConnectorException
	{
		QueueSource qs = new QueueSource(1);
		qs.addEvent(0);
		ThreadPullableTest.DelayProcessor dp = new ThreadPullableTest.DelayProcessor(1, 1000);
		PullPipeline pp = new PullPipeline(dp);
		Connector.connect(qs, pp);
		Pullable p = pp.getPullableOutput();
		pp.start();
		long last_time = System.currentTimeMillis();
		for (int i = 0; i < 10; i++)
		{
			Object o = p.pull();
			long this_time = System.currentTimeMillis();
			long elapsed = this_time - last_time;
			last_time = this_time;
			assertNotNull(o);
			System.out.println(elapsed);
		}
		pp.stop();
	}
	
	@Test
	public void test2() throws ConnectorException
	{
		QueueSource qs = new QueueSource(1);
		qs.addEvent(0);
		ThreadPullableTest.DelayProcessor dp = new ThreadPullableTest.DelayProcessor(1, 1000);
		Connector.connect(qs, dp);
		Pullable p = dp.getPullableOutput();
		long last_time = System.currentTimeMillis();
		for (int i = 0; i < 10; i++)
		{
			Object o = p.pull();
			long this_time = System.currentTimeMillis();
			long elapsed = this_time - last_time;
			last_time = this_time;
			assertNotNull(o);
			System.out.println(elapsed);
		}
	}

}
