package ca.uqac.lif.cep.concurrency;

import static org.junit.Assert.*;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSource;

public class PullPipelineTest 
{
	@Test(timeout=10000)
	public void testWithoutThreads1() throws ConnectorException
	{
		ThreadManager tm = new ThreadManager(0);
		QueueSource qs = new QueueSource(1);
		qs.addEvent(0);
		ThreadPullableTest.DelayProcessor dp = new ThreadPullableTest.DelayProcessor(1, 1000);
		PullPipeline pp = new PullPipeline(dp, tm);
		Connector.connect(qs, pp);
		Pullable p = pp.getPullableOutput();
		pp.start();
		long last_time = System.currentTimeMillis();
		for (int i = 0; i < 5; i++)
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
	
	@Test(timeout=10000)
	public void testWithUnlimitedThreads1() throws ConnectorException
	{
		ThreadManager tm = new ThreadManager(-1); // Unlimited threads
		QueueSource qs = new QueueSource(1);
		qs.addEvent(0);
		ThreadPullableTest.DelayProcessor dp = new ThreadPullableTest.DelayProcessor(1, 1000);
		PullPipeline pp = new PullPipeline(dp, tm);
		Connector.connect(qs, pp);
		Pullable p = pp.getPullableOutput();
		pp.start();
		long last_time = System.currentTimeMillis();
		for (int i = 0; i < 5; i++)
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
	
	@Test(timeout=10000)
	public void testWithTwoThreads1() throws ConnectorException
	{
		ThreadManager tm = new ThreadManager(4);
		QueueSource qs = new QueueSource(1);
		qs.addEvent(0);
		ThreadPullableTest.DelayProcessor dp = new ThreadPullableTest.DelayProcessor(1, 1000);
		PullPipeline pp = new PullPipeline(dp, tm);
		Connector.connect(qs, pp);
		Pullable p = pp.getPullableOutput();
		pp.start();
		long first_time = System.currentTimeMillis();
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
		System.out.println("Total duration: " + (last_time - first_time));
		pp.stop();
	}
	
	@Test(timeout=12000)
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
	
	@Test(timeout=10000)
	public void testClone1() throws ConnectorException
	{
		GroupProcessor gp = new GroupProcessor(0, 1);
		QueueSource qs = new QueueSource(1);
		qs.addEvent(0);
		Passthrough pt = new Passthrough(1);
		PullPipeline pp = new PullPipeline(pt);
		Connector.connect(qs, pp);
		gp.addProcessors(qs, pp);
		gp.associateOutput(0, pp, 0);
		GroupProcessor gp2 = gp.clone();
		Pullable p = gp2.getPullableOutput();
		gp2.start();
		Object o = p.pull();
		assertNotNull(o);
	}
}
