package ca.uqac.lif.cep;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import ca.uqac.lif.cep.tmf.Passthrough;

/**
 * Unit tests for the {@link UniformProcessor} class.
 */
public class UniformProcessorTest 
{	
	@Test
	public void testSamePullable()
	{
		Passthrough pt = new Passthrough();
		Pullable p1 = pt.getPullableOutput(0);
		Pullable p2 = pt.getPullableOutput(0);
		assertTrue(p1 == p2);
	}
	
	@Test
	public void testSamePushable()
	{
		Passthrough pt = new Passthrough();
		Pushable p1 = pt.getPushableInput(0);
		Pushable p2 = pt.getPushableInput(0);
		assertTrue(p1 == p2);
	}

}
