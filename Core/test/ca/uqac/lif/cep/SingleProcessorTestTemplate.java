package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import java.util.ArrayDeque;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.clone.IdentityPrintHandler;
import ca.uqac.lif.azrael.clone.IdentityReadHandler;
import ca.uqac.lif.azrael.clone.ReadableReadHandler;
import ca.uqac.lif.cep.tmf.QueueSource;

public class SingleProcessorTestTemplate 
{
	@Test
	public void testDummy1()
	{
		assertTrue(true);
	}
	
	/**
	 * Checks the declared input and output arity
	 * @param p The processor to test on
	 * @param in_arity The expected input arity
	 * @param out_arity The expected output arity
	 */
	public static void checkArity(Processor p, int in_arity, int out_arity)
	{
		assertEquals(in_arity, p.getInputArity());
		assertEquals(out_arity, p.getOutputArity());
	}
	
	/**
	 * Tests the behaviour of the processor when being duplicated.
	 * Conditions to be followed:
	 * <ol>
	 * <li>Duplicating results in a non-null object of the same class as the
	 * original, and the same input/output arity</li>
	 * <li>The context contents are preserved in the duplicate</li>
	 * <li>The context contents are independent from the original's context
	 * object</li>
	 * </ol>
	 * @param p The processor to test on
	 */
	public static void checkDuplicate1(Processor p)
	{
		p.setContext("foo", "bar");
		Processor dup = p.duplicate();
		assertNotNull(dup);
		assertEquals(p.getClass(), dup.getClass());
		assertEquals(p.getInputArity(), dup.getInputArity());
		assertEquals(p.getOutputArity(), dup.getOutputArity());
		assertEquals("bar", dup.getContext("foo"));
		p.setContext("baz", "123");
		assertNull(dup.getContext("baz"));
	}
	
	/**
	 * Checks that each input pushable given by the processor is not null, and
	 * that asking twice for the same pushable returns the same object.
	 * @param p The processor to test on
	 */
	public static void checkMultiplePushable1(Processor p)
	{
		for (int i = 0; i < p.getInputArity(); i++)
		{
			Pushable push = p.getPushableInput(i);
			assertNotNull(push);
			Pushable push2 = p.getPushableInput(i);
			assertEquals(push, push2);
		}
	}
	
	/**
	 * Checks that each output pullable given by the processor is not null, and
	 * that asking twice for the same pullable returns the same object.
	 * @param p The processor to test on
	 */
	public static void checkMultiplePullable1(Processor p)
	{
		for (int i = 0; i < p.getOutputArity(); i++)
		{
			Pullable pull = p.getPullableOutput(i);
			assertNotNull(pull);
			Pullable pull2 = p.getPullableOutput(i);
			assertEquals(pull, pull2);
		}
	}

}
