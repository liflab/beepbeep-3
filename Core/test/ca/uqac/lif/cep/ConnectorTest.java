package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.SingleProcessorTestTemplate.SingleProcessorWrapper;

public class ConnectorTest 
{
	@Test
	public void testArity1()
	{
		SingleProcessorWrapper spw1 = new SingleProcessorWrapper(1, 1);
		SingleProcessorWrapper spw2 = new SingleProcessorWrapper(1, 1);
		Connector.connect(spw1, spw2);
		assertEquals(spw1, spw2.getInputPullable(0).getObject());
		assertEquals(spw2, spw1.getOutputPushable(0).getObject());
	}
	
	@Test
	public void testArity2()
	{
		SingleProcessorWrapper spw1 = new SingleProcessorWrapper(2, 2);
		SingleProcessorWrapper spw2 = new SingleProcessorWrapper(2, 2);
		// We deliberately interlace to make sure the indices are correctly kept
		Connector.connect(spw1, 0, spw2, 1);
		Connector.connect(spw1, 1, spw2, 0);
		assertEquals(spw1, spw2.getInputPullable(0).getObject());
		assertEquals(spw2, spw1.getOutputPushable(0).getObject());
		assertEquals(1, spw2.getInputPullable(0).getIndex());
		assertEquals(1, spw1.getOutputPushable(0).getIndex());
		assertEquals(spw1, spw2.getInputPullable(1).getObject());
		assertEquals(spw2, spw1.getOutputPushable(1).getObject());
		assertEquals(0, spw2.getInputPullable(1).getIndex());
		assertEquals(0, spw1.getOutputPushable(1).getIndex());
	}
	
	@Test(expected = ConnectorException.class)
	public void testInputOutOfBounds()
	{
		SingleProcessorWrapper spw1 = new SingleProcessorWrapper(1, 1);
		SingleProcessorWrapper spw2 = new SingleProcessorWrapper(1, 1);
		Connector.connect(spw1, 1, spw2, 0);
	}
	
	@Test(expected = ConnectorException.class)
	public void testOutputOutOfBounds()
	{
		SingleProcessorWrapper spw1 = new SingleProcessorWrapper(1, 1);
		SingleProcessorWrapper spw2 = new SingleProcessorWrapper(1, 1);
		Connector.connect(spw1, 0, spw2, 1);
	}
	
	/**
	 * Checks that connecting a processor with output type A to a processor
	 * with input type B throws an exception if A is not a descendant of B.
	 */
	@Test(expected = ConnectorException.class)
	public void testTypes1()
	{
		SingleProcessorWrapper spw1 = new SingleProcessorWrapper(1, 1);
		spw1.setOutputType(Processor.class);
		SingleProcessorWrapper spw2 = new SingleProcessorWrapper(1, 1);
		spw2.setInputType(Number.class);
		Connector.connect(spw1, spw2);
	}
	
	/**
	 * Checks that connecting a processor with output type A to a processor
	 * with input type B works if A is a descendant of B.
	 */
	@Test
	public void testTypes2()
	{
		SingleProcessorWrapper spw1 = new SingleProcessorWrapper(1, 1);
		spw1.setOutputType(Integer.class);
		SingleProcessorWrapper spw2 = new SingleProcessorWrapper(1, 1);
		spw2.setInputType(Number.class);
		Connector.connect(spw1, spw2);
	}
	
	/**
	 * Checks that the use of {@link Typed.Variant} bypasses the type 
	 * verification.
	 */
	@Test
	public void testTypes3()
	{
		SingleProcessorWrapper spw1 = new SingleProcessorWrapper(1, 1);
		spw1.setOutputType(Typed.Variant.class);
		SingleProcessorWrapper spw2 = new SingleProcessorWrapper(1, 1);
		spw2.setInputType(Number.class);
		Connector.connect(spw1, spw2);
	}
	
	/**
	 * Checks that the use of {@link Typed.Variant} bypasses the type 
	 * verification (other direction).
	 */
	@Test
	public void testTypes4()
	{
		SingleProcessorWrapper spw1 = new SingleProcessorWrapper(1, 1);
		spw1.setOutputType(Integer.class);
		SingleProcessorWrapper spw2 = new SingleProcessorWrapper(1, 1);
		spw2.setInputType(Typed.Variant.class);
		Connector.connect(spw1, spw2);
	}
}
