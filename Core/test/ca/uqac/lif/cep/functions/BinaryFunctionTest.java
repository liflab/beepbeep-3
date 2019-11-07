package ca.uqac.lif.cep.functions;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Map;

import org.junit.Test;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.petitpoucet.Designator.Nothing;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.common.Context;
import ca.uqac.lif.petitpoucet.functions.BinaryFunction;
import ca.uqac.lif.petitpoucet.functions.FunctionQueryable;
import ca.uqac.lif.petitpoucet.functions.BinaryFunction.BinaryFunctionQueryable;
import ca.uqac.lif.petitpoucet.functions.BinaryFunction.BinaryFunctionQueryable.Inputs;
import ca.uqac.lif.petitpoucet.graph.AndNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteObjectNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;
import ca.uqac.lif.petitpoucet.graph.OrNode;

public class BinaryFunctionTest 
{
	@Test
	public void testEvaluate()
	{
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		Object[] outputs = new Object[1];
		FunctionQueryable fq = tbf.evaluate(new Object[] {3, "foo"}, outputs);
		assertEquals(6, outputs[0]);
		assertNotNull(fq);
	}
	
	@Test
	public void testCreate() throws PrintException
	{
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		assertEquals(2, tbf.getInputArity());
		assertEquals(1, tbf.getOutputArity());
		assertEquals(Number.class, tbf.getInputType(0));
		assertEquals(String.class, tbf.getInputType(1));
		assertNull(tbf.getInputType(2));
		assertEquals(Object.class, tbf.getOutputType(0));
	}
	
	@Test
	public void testReset() throws PrintException
	{
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		tbf.setState(314);
		assertEquals(314, tbf.getState());
		tbf.reset();
		assertEquals(0, tbf.getState());
	}
	
	@Test
	public void testDuplicateState() throws PrintException
	{
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		tbf.setState(314);
		TestableBinaryFunction tbf_dup = tbf.duplicate(true);
		assertFalse(tbf == tbf_dup);
		assertEquals(314, tbf_dup.getState());
	}
	
	@Test
	public void testDuplicateNoState() throws PrintException
	{
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		tbf.setState(314);
		TestableBinaryFunction tbf_dup = (TestableBinaryFunction) tbf.duplicate();
		assertFalse(tbf == tbf_dup);
		assertEquals(0, tbf_dup.getState());
	}
	
	@Test
	public void testPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		assertNull(iop.print(tbf));
		
	}
	
	@Test
	public void testRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		TestableBinaryFunction tbf = new TestableBinaryFunction().read(ior, null);
		assertNotNull(tbf);
	}
	
	@Test
	public void testQueryableCausalityBoth()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.BOTH);
		assertEquals("foo", bfq.getReference());
		assertEquals(2, bfq.getInputArity());
		assertEquals(1, bfq.getOutputArity());
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(TraceabilityQuery.CausalityQuery.instance, NthOutput.get(0), root, factory);
		assertEquals(1, root.getChildren().size());
		assertTrue(root.getChildren().get(0).getNode() instanceof AndNode);
		assertEquals(2, leaves.size());
		ConcreteObjectNode leaf1 = (ConcreteObjectNode) leaves.get(0);
		NthInput ni1 = (NthInput) leaf1.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni1.getIndex());
		assertEquals(bfq, leaf1.getDesignatedObject().getObject());
		ConcreteObjectNode leaf2 = (ConcreteObjectNode) leaves.get(0);
		NthInput ni2 = (NthInput) leaf2.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni2.getIndex());
		assertEquals(bfq, leaf2.getDesignatedObject().getObject());
	}
	
	@Test
	public void testQueryableCausalityAny()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.ANY);
		assertEquals("foo", bfq.getReference());
		assertEquals(2, bfq.getInputArity());
		assertEquals(1, bfq.getOutputArity());
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(TraceabilityQuery.CausalityQuery.instance, NthOutput.get(0), root, factory);
		assertEquals(1, root.getChildren().size());
		assertTrue(root.getChildren().get(0).getNode() instanceof OrNode);
		assertEquals(2, leaves.size());
		ConcreteObjectNode leaf1 = (ConcreteObjectNode) leaves.get(0);
		NthInput ni1 = (NthInput) leaf1.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni1.getIndex());
		assertEquals(bfq, leaf1.getDesignatedObject().getObject());
		ConcreteObjectNode leaf2 = (ConcreteObjectNode) leaves.get(0);
		NthInput ni2 = (NthInput) leaf2.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni2.getIndex());
		assertEquals(bfq, leaf2.getDesignatedObject().getObject());
	}
	
	@Test
	public void testQueryableCausalityLeft()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.LEFT);
		assertEquals("foo", bfq.getReference());
		assertEquals(2, bfq.getInputArity());
		assertEquals(1, bfq.getOutputArity());
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(TraceabilityQuery.CausalityQuery.instance, NthOutput.get(0), root, factory);
		assertEquals(1, root.getChildren().size());
		assertTrue(root.getChildren().get(0).getNode() instanceof ConcreteObjectNode);
		assertEquals(1, leaves.size());
		ConcreteObjectNode leaf1 = (ConcreteObjectNode) leaves.get(0);
		NthInput ni1 = (NthInput) leaf1.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni1.getIndex());
		assertEquals(bfq, leaf1.getDesignatedObject().getObject());
	}
	
	@Test
	public void testQueryableCausalityRight()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.RIGHT);
		assertEquals("foo", bfq.getReference());
		assertEquals(2, bfq.getInputArity());
		assertEquals(1, bfq.getOutputArity());
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(TraceabilityQuery.CausalityQuery.instance, NthOutput.get(0), root, factory);
		assertEquals(1, root.getChildren().size());
		assertTrue(root.getChildren().get(0).getNode() instanceof ConcreteObjectNode);
		assertEquals(1, leaves.size());
		ConcreteObjectNode leaf1 = (ConcreteObjectNode) leaves.get(0);
		NthInput ni1 = (NthInput) leaf1.getDesignatedObject().getDesignator().peek();
		assertEquals(1, ni1.getIndex());
		assertEquals(bfq, leaf1.getDesignatedObject().getObject());
	}
	
	@Test
	public void testQueryableConsequenceBoth()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.BOTH);
		assertEquals("foo", bfq.getReference());
		assertEquals(2, bfq.getInputArity());
		assertEquals(1, bfq.getOutputArity());
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(TraceabilityQuery.ConsequenceQuery.instance, NthInput.get(0), root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode leaf1 = (ConcreteObjectNode) leaves.get(0);
		NthOutput ni1 = (NthOutput) leaf1.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni1.getIndex());
		assertEquals(bfq, leaf1.getDesignatedObject().getObject());
		leaves = bfq.query(TraceabilityQuery.ConsequenceQuery.instance, NthInput.get(1), root, factory);
		ConcreteObjectNode leaf2 = (ConcreteObjectNode) leaves.get(0);
		NthOutput ni2 = (NthOutput) leaf2.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni2.getIndex());
		assertEquals(bfq, leaf2.getDesignatedObject().getObject());
	}
	
	@Test
	public void testQueryableConsequenceAny()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.ANY);
		assertEquals("foo", bfq.getReference());
		assertEquals(2, bfq.getInputArity());
		assertEquals(1, bfq.getOutputArity());
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(TraceabilityQuery.ConsequenceQuery.instance, NthInput.get(0), root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode leaf1 = (ConcreteObjectNode) leaves.get(0);
		NthOutput ni1 = (NthOutput) leaf1.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni1.getIndex());
		assertEquals(bfq, leaf1.getDesignatedObject().getObject());
		leaves = bfq.query(TraceabilityQuery.ConsequenceQuery.instance, NthInput.get(1), root, factory);
		ConcreteObjectNode leaf2 = (ConcreteObjectNode) leaves.get(0);
		NthOutput ni2 = (NthOutput) leaf2.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni2.getIndex());
		assertEquals(bfq, leaf2.getDesignatedObject().getObject());
	}
	
	@Test
	public void testQueryableConsequenceLeft()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.LEFT);
		assertEquals("foo", bfq.getReference());
		assertEquals(2, bfq.getInputArity());
		assertEquals(1, bfq.getOutputArity());
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(TraceabilityQuery.ConsequenceQuery.instance, NthInput.get(0), root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode leaf1 = (ConcreteObjectNode) leaves.get(0);
		NthOutput ni1 = (NthOutput) leaf1.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni1.getIndex());
		assertEquals(bfq, leaf1.getDesignatedObject().getObject());
		leaves = bfq.query(TraceabilityQuery.ConsequenceQuery.instance, NthInput.get(1), root, factory);
		ConcreteObjectNode leaf2 = (ConcreteObjectNode) leaves.get(0);
		assertTrue(leaf2.getDesignatedObject().getDesignator() instanceof Nothing);
	}
	
	@Test
	public void testQueryableConsequenceRight()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.RIGHT);
		assertEquals("foo", bfq.getReference());
		assertEquals(2, bfq.getInputArity());
		assertEquals(1, bfq.getOutputArity());
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = bfq.query(TraceabilityQuery.ConsequenceQuery.instance, NthInput.get(1), root, factory);
		assertEquals(1, leaves.size());
		ConcreteObjectNode leaf1 = (ConcreteObjectNode) leaves.get(0);
		NthOutput ni1 = (NthOutput) leaf1.getDesignatedObject().getDesignator().peek();
		assertEquals(0, ni1.getIndex());
		assertEquals(bfq, leaf1.getDesignatedObject().getObject());
		leaves = bfq.query(TraceabilityQuery.ConsequenceQuery.instance, NthInput.get(0), root, factory);
		ConcreteObjectNode leaf2 = (ConcreteObjectNode) leaves.get(0);
		assertTrue(leaf2.getDesignatedObject().getDesignator() instanceof Nothing);
	}
	
	@Test
	public void testQueryableDuplicateState()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.RIGHT);
		BinaryFunctionQueryable bfq_dup = (BinaryFunctionQueryable) bfq.duplicate();
		assertNotNull(bfq_dup);
		assertFalse(bfq == bfq_dup);
		assertEquals(bfq.m_inputs, bfq_dup.m_inputs);
	}
	
	@Test
	public void testQueryableDuplicateNoState()
	{
		BinaryFunctionQueryable bfq = new BinaryFunctionQueryable("foo", Inputs.RIGHT);
		BinaryFunctionQueryable bfq_dup = (BinaryFunctionQueryable) bfq.duplicate(true);
		assertNotNull(bfq_dup);
		assertFalse(bfq == bfq_dup);
		assertEquals(bfq.m_inputs, bfq_dup.m_inputs);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testQueryablePrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		BinaryFunctionQueryable bfq;
		int x;
		bfq = new BinaryFunctionQueryable("foo", Inputs.LEFT);
		x = (Integer) ((Map<String,Object>) iop.print(bfq)).get(FunctionQueryable.s_contentsKey);
		assertEquals(1, x);
		bfq = new BinaryFunctionQueryable("foo", Inputs.RIGHT);
		x = (Integer) ((Map<String,Object>) iop.print(bfq)).get(FunctionQueryable.s_contentsKey);
		assertEquals(2, x);
		bfq = new BinaryFunctionQueryable("foo", Inputs.ANY);
		x = (Integer) ((Map<String,Object>) iop.print(bfq)).get(FunctionQueryable.s_contentsKey);
		assertEquals(3, x);
		bfq = new BinaryFunctionQueryable("foo", Inputs.BOTH);
		x = (Integer) ((Map<String,Object>) iop.print(bfq)).get(FunctionQueryable.s_contentsKey);
		assertEquals(0, x);
	}
	
	@Test
	public void testQueryableRead1() throws ReadException
	{
		Map<String,Object> printed = FunctionQueryableTest.getPrintedMap("foo", 2, 1, 3);
		IdentityObjectReader ior = new IdentityObjectReader();
		BinaryFunctionQueryable bfq = (BinaryFunctionQueryable) new BinaryFunctionQueryable("", Inputs.BOTH).read(ior, printed);
		assertNotNull(bfq);
		assertEquals("foo", bfq.getReference());
		assertEquals(Inputs.ANY, bfq.m_inputs);
	}
	
	@Test
	public void testQueryableRead2() throws ReadException
	{
		Map<String,Object> printed = FunctionQueryableTest.getPrintedMap("foo", 2, 1, 2);
		IdentityObjectReader ior = new IdentityObjectReader();
		BinaryFunctionQueryable bfq = (BinaryFunctionQueryable) new BinaryFunctionQueryable("", Inputs.BOTH).read(ior, printed);
		assertNotNull(bfq);
		assertEquals("foo", bfq.getReference());
		assertEquals(Inputs.RIGHT, bfq.m_inputs);
	}
	
	@Test
	public void testQueryableRead3() throws ReadException
	{
		Map<String,Object> printed = FunctionQueryableTest.getPrintedMap("foo", 2, 1, 1);
		IdentityObjectReader ior = new IdentityObjectReader();
		BinaryFunctionQueryable bfq = (BinaryFunctionQueryable) new BinaryFunctionQueryable("", Inputs.BOTH).read(ior, printed);
		assertNotNull(bfq);
		assertEquals("foo", bfq.getReference());
		assertEquals(Inputs.LEFT, bfq.m_inputs);
	}
	
	@Test
	public void testQueryableRead4() throws ReadException
	{
		Map<String,Object> printed = FunctionQueryableTest.getPrintedMap("foo", 2, 1, 0);
		IdentityObjectReader ior = new IdentityObjectReader();
		BinaryFunctionQueryable bfq = (BinaryFunctionQueryable) new BinaryFunctionQueryable("", Inputs.BOTH).read(ior, printed);
		assertNotNull(bfq);
		assertEquals("foo", bfq.getReference());
		assertEquals(Inputs.BOTH, bfq.m_inputs);
	}
	
	@Test(expected = ReadException.class)
	public void testQueryableReadInvalid() throws ReadException
	{
		Map<String,Object> printed = FunctionQueryableTest.getPrintedMap("foo", 2, 1, "arf");
		IdentityObjectReader ior = new IdentityObjectReader();
		new BinaryFunctionQueryable("", Inputs.BOTH).read(ior, printed);
	}
	
	public static class TestableBinaryFunction extends BinaryFunction<Number,String,Object>
	{
		/**
		 * Dummy state variable
		 */
		protected Object m_state;
		
		public TestableBinaryFunction()
		{
			super(Number.class, String.class, Object.class);
			m_state = 0;
		}

		@Override
		public TestableBinaryFunction duplicate(boolean with_state) 
		{
			TestableBinaryFunction tbf = new TestableBinaryFunction();
			if (with_state)
			{
				tbf.m_state = m_state;
			}
			return tbf;
		}

		@Override
		public BinaryFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c)
		{
			outputs[0] = ((Integer) inputs[0]).intValue() + ((String) inputs[1]).length();
			return new BinaryFunctionQueryable(toString(), Inputs.BOTH);
		}
		
		public Object getState()
		{
			return m_state;
		}
		
		public void setState(Object o)
		{
			m_state = o;
		}
		
		@Override
		public void reset()
		{
			super.reset();
			m_state = 0;
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException
		{
			return null;
		}

		@Override
		public TestableBinaryFunction read(ObjectReader<?> reader, Object o) throws ReadException
		{
			return new TestableBinaryFunction();
		} 
	}
}
