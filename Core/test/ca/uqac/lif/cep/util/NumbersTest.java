package ca.uqac.lif.cep.util;

import static org.junit.Assert.*;

import java.util.List;

import org.junit.Test;

import ca.uqac.lif.cep.functions.BinaryFunction.BinaryFunctionQueryable;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.CausalityQuery;
import ca.uqac.lif.petitpoucet.TraceabilityQuery.ProvenanceQuery;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.graph.ConcreteObjectNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;
import ca.uqac.lif.petitpoucet.graph.OrNode;

public class NumbersTest 
{
	@Test
	public void testAdditionQueryableProvenance1()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.addition.evaluate(new Object[] {3, 2}, outputs);
		ConcreteTracer factory = new ConcreteTracer();
		List<TraceabilityNode> leaves = bfq.query(ProvenanceQuery.instance, new NthOutput(0), factory.getAndNode(), factory);
		assertEquals(2, leaves.size());
		ConcreteObjectNode left = (ConcreteObjectNode) leaves.get(0);
		Designator d_left = left.getDesignatedObject().getDesignator();
		assertEquals(0, ((NthInput) d_left.peek()).getIndex());
		ConcreteObjectNode right = (ConcreteObjectNode) leaves.get(1);
		Designator d_right = right.getDesignatedObject().getDesignator();
		assertEquals(1, ((NthInput) d_right.peek()).getIndex());
	}
	
	@Test
	public void testMultiplicationQueryableCausality1()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {3, 2}, outputs);
		ConcreteTracer factory = new ConcreteTracer();
		List<TraceabilityNode> leaves = bfq.query(CausalityQuery.instance, new NthOutput(0), factory.getAndNode(), factory);
		assertEquals(2, leaves.size());
		ConcreteObjectNode left = (ConcreteObjectNode) leaves.get(0);
		Designator d_left = left.getDesignatedObject().getDesignator();
		assertEquals(0, ((NthInput) d_left.peek()).getIndex());
		ConcreteObjectNode right = (ConcreteObjectNode) leaves.get(1);
		Designator d_right = right.getDesignatedObject().getDesignator();
		assertEquals(1, ((NthInput) d_right.peek()).getIndex());
	}
	
	@Test
	public void testMultiplicationQueryableCausality2()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {0, 2}, outputs);
		ConcreteTracer factory = new ConcreteTracer();
		List<TraceabilityNode> leaves = bfq.query(CausalityQuery.instance, new NthOutput(0), factory.getAndNode(), factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode left = (ConcreteObjectNode) leaves.get(0);
		Designator d_left = left.getDesignatedObject().getDesignator();
		assertEquals(0, ((NthInput) d_left.peek()).getIndex());
	}
	
	@Test
	public void testMultiplicationQueryableCausality3()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {2, 0}, outputs);
		ConcreteTracer factory = new ConcreteTracer();
		List<TraceabilityNode> leaves = bfq.query(CausalityQuery.instance, new NthOutput(0), factory.getAndNode(), factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode left = (ConcreteObjectNode) leaves.get(0);
		Designator d_left = left.getDesignatedObject().getDesignator();
		assertEquals(1, ((NthInput) d_left.peek()).getIndex());
	}
	
	@Test
	public void testMultiplicationQueryableCausality4()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {0, 0}, outputs);
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(CausalityQuery.instance, new NthOutput(0), root, factory);
		assertEquals(1, root.getChildren().size());
		assertTrue(root.getChildren().get(0).getNode() instanceof OrNode);
		assertEquals(2, leaves.size());
	}
	
	@Test
	public void testSum1()
	{
		Object[] outputs = new Object[1];
		Numbers.Sum sum = new Numbers.Sum();
		sum.evaluate(new Object[] {1}, outputs);
		assertEquals(1f, outputs[0]);
		sum.evaluate(new Object[] {2}, outputs);
		assertEquals(3f, outputs[0]);
		sum.devaluate(new Object[] {1}, outputs);
		assertEquals(2f, outputs[0]);
	}
}
