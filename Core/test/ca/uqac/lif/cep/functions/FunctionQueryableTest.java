package ca.uqac.lif.cep.functions;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;

public class FunctionQueryableTest
{
	@Test
	public void testQueryInputTaint()
	{
		FunctionQueryable fq = new FunctionQueryable("foo", 3, 2);
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = fq.query(TraceabilityQuery.TaintQuery.instance, new NthInput(2), root, factory);
		assertEquals(2, leaves.size());
	}
	
	@Test
	public void testQueryInputConsequence()
	{
		FunctionQueryable fq = new FunctionQueryable("foo", 3, 2);
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = fq.query(TraceabilityQuery.ConsequenceQuery.instance, new NthInput(2), root, factory);
		assertEquals(2, leaves.size());
	}
	
	@Test
	public void testQueryOutputProvenance()
	{
		FunctionQueryable fq = new FunctionQueryable("foo", 3, 2);
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = fq.query(TraceabilityQuery.ProvenanceQuery.instance, new NthOutput(1), root, factory);
		assertEquals(3, leaves.size());
	}
	
	@Test
	public void testQueryOutputCausality()
	{
		FunctionQueryable fq = new FunctionQueryable("foo", 3, 2);
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = fq.query(TraceabilityQuery.CausalityQuery.instance, new NthOutput(1), root, factory);
		assertEquals(3, leaves.size());
	}
	
	@Test
	public void testDuplicateState()
	{
		FunctionQueryable fq = new FunctionQueryable("foo", 3, 2);
		FunctionQueryable fq_dup = fq.duplicate(true);
		assertNotNull(fq_dup);
		assertFalse(fq == fq_dup);
		assertEquals("foo", fq_dup.getReference());
		assertEquals(3, fq_dup.getInputArity());
		assertEquals(2, fq_dup.getOutputArity());
	}
	
	@Test
	public void testDuplicateNoState()
	{
		FunctionQueryable fq = new FunctionQueryable("foo", 3, 2);
		FunctionQueryable fq_dup = fq.duplicate();
		assertNotNull(fq_dup);
		assertFalse(fq == fq_dup);
		assertEquals("foo", fq_dup.getReference());
		assertEquals(3, fq_dup.getInputArity());
		assertEquals(2, fq_dup.getOutputArity());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		FunctionQueryable fq = new FunctionQueryable("foo", 3, 2);
		Map<String,Object> printed = (Map<String,Object>) iop.print(fq);
		assertNotNull(printed);
		assertEquals(2, printed.size());
		assertEquals("foo", printed.get(FunctionQueryable.s_referenceKey));
		List<Integer> arities = (List<Integer>) printed.get(FunctionQueryable.s_arityKey);
		assertEquals(2, arities.size());
		assertEquals(3, (int) arities.get(0));
		assertEquals(2, (int) arities.get(1));
	}
	
	@Test
	public void testRead() throws ReadException
	{
		Map<String,Object> printed = getPrintedMap("foo", 3, 2, "arf");
		IdentityObjectReader ior = new IdentityObjectReader();
		FunctionQueryable fq = new FunctionQueryable("", 0, 0).read(ior, printed);
		assertNotNull(fq);
		assertEquals(3, fq.getInputArity());
		assertEquals(2, fq.getOutputArity());
		assertEquals("foo", fq.getReference());
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid1() throws ReadException
	{
		Map<String,Object> printed = getPrintedMap("foo", 3, 2, "arf");
		printed.remove(FunctionQueryable.s_referenceKey);
		IdentityObjectReader ior = new IdentityObjectReader();
		new FunctionQueryable("", 0, 0).read(ior, printed);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid2() throws ReadException
	{
		Map<String,Object> printed = getPrintedMap("foo", 3, 2, "arf");
		printed.remove(FunctionQueryable.s_arityKey);
		IdentityObjectReader ior = new IdentityObjectReader();
		new FunctionQueryable("", 0, 0).read(ior, printed);
	}
	
	@SuppressWarnings("unchecked")
	@Test(expected = ReadException.class)
	public void testReadInvalid3() throws ReadException
	{
		Map<String,Object> printed = getPrintedMap("foo", 3, 2, "arf");
		((List<Integer>) printed.get(FunctionQueryable.s_arityKey)).remove(0);
		IdentityObjectReader ior = new IdentityObjectReader();
		new FunctionQueryable("", 0, 0).read(ior, printed);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid4() throws ReadException
	{
		Map<String,Object> printed = getPrintedMap("foo", 3, 2, "arf");
		printed.put(FunctionQueryable.s_arityKey, "foo");
		IdentityObjectReader ior = new IdentityObjectReader();
		new FunctionQueryable("", 0, 0).read(ior, printed);
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid5() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		new FunctionQueryable("", 0, 0).read(ior, "foo");
	}
	
	public static Map<String,Object> getPrintedMap(String reference, int in_arity, int out_arity, Object contents)
	{
		Map<String,Object> printed = new HashMap<String,Object>();
		printed.put(FunctionQueryable.s_referenceKey, reference);
		List<Integer> arities = new ArrayList<Integer>(2);
		arities.add(in_arity);
		arities.add(out_arity);
		printed.put(FunctionQueryable.s_arityKey, arities);
		if (contents != null)
		{
			printed.put(FunctionQueryable.s_contentsKey, contents);
		}
		return printed;
	}
}
