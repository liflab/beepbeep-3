package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.TestUtilities.TestableSingleProcessor;

public class ConnectorTest 
{
	@Test
	public void testArity1()
	{
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		Connector.connect(spw1, spw2);
		assertEquals(spw1, spw2.getInputPullable(0).getObject());
		assertEquals(spw2, spw1.getOutputPushable(0).getObject());
	}
	
	@Test
	public void testArity2()
	{
		TestableSingleProcessor spw1 = new TestableSingleProcessor(2, 2);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(2, 2);
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
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		Connector.connect(spw1, 1, spw2, 0);
	}
	
	@Test(expected = ConnectorException.class)
	public void testOutputOutOfBounds()
	{
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		Connector.connect(spw1, 0, spw2, 1);
	}
	
	/**
	 * Checks that connecting a processor with output type A to a processor
	 * with input type B throws an exception if A is not a descendant of B.
	 */
	@Test(expected = ConnectorException.class)
	public void testTypes1()
	{
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		spw1.setOutputType(Processor.class);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
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
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		spw1.setOutputType(Integer.class);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
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
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		spw1.setOutputType(Typed.Variant.class);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
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
		TestableSingleProcessor spw1 = new TestableSingleProcessor(1, 1);
		spw1.setOutputType(Integer.class);
		TestableSingleProcessor spw2 = new TestableSingleProcessor(1, 1);
		spw2.setInputType(Typed.Variant.class);
		Connector.connect(spw1, spw2);
	}
}
