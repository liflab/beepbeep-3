package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import org.junit.Test;

import ca.uqac.lif.cep.epl.QueueSource;

public class PullableTest 
{
	@Test
	public void testTypedPullable1()
	{
		QueueSource qs = new QueueSource("A", 1);
		Passthrough pt = new Passthrough(1);
		Connector.connect(qs, pt);
		Pullable p = pt.getPullableOutput(0);
		TypedPullable<String> tp = new TypedPullable<String>(p);
		assertEquals(Pullable.NextStatus.YES, tp.hasNext());
		String s = tp.pull();
		assertEquals("A", s);
		assertEquals(1, tp.getPullCount());
	}
	
	@Test
	public void testTypedPullable2()
	{
		QueueSource qs = new QueueSource("A", 1);
		Passthrough pt = new Passthrough(1);
		Connector.connect(qs, pt);
		Pullable p = pt.getPullableOutput(0);
		TypedPullable<String> tp = new TypedPullable<String>(p);
		assertEquals(Pullable.NextStatus.YES, tp.hasNextHard());
		String s = tp.pullHard();
		assertEquals("A", s);
		assertEquals(1, tp.getPullCount());
	}

}
