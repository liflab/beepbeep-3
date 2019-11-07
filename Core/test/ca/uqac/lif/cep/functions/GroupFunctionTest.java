package ca.uqac.lif.cep.functions;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Test;

import ca.uqac.lif.cep.functions.BinaryFunctionTest.TestableBinaryFunction;
import ca.uqac.lif.petitpoucet.ObjectNode;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.functions.CircuitFunction;
import ca.uqac.lif.petitpoucet.functions.GroupFunction;
import ca.uqac.lif.petitpoucet.functions.CircuitFunction.CircuitFunctionQueryable;
import ca.uqac.lif.petitpoucet.functions.Function.FunctionException;
import ca.uqac.lif.petitpoucet.functions.FunctionConnector.FunctionConnection;
import ca.uqac.lif.petitpoucet.functions.GroupFunction.CircuitFunctionPlaceholder;
import ca.uqac.lif.petitpoucet.functions.GroupFunction.GroupFunctionQueryable;
import ca.uqac.lif.petitpoucet.functions.numbers.Numbers;
import ca.uqac.lif.petitpoucet.circuit.CircuitQueryable;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;

public class GroupFunctionTest 
{
	@Test
	public void testTypes()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		CircuitFunction cf = new CircuitFunction(tbf);
		gf.add(cf);
		gf.associateInput(0, cf, 1);
		gf.associateInput(1, cf, 0);
		gf.associateOutput(0, cf, 0);
		assertEquals(String.class, gf.getInputType(0));
		assertEquals(Number.class, gf.getInputType(1));
		assertEquals(Object.class, gf.getOutputType(0));
	}
	
	@Test(expected = FunctionException.class)
	public void testTypesOutputOutOfBounds()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		gf.getOutputType(1);
	}
	
	@Test(expected = FunctionException.class)
	public void testTypesInputOutOfBounds()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		gf.getInputType(3);
	}
	
	@Test
	public void testContext()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		gf.setContext("foo", "bar");
		assertEquals("bar", gf.getContext("foo"));
	}
	
	@Test
	public void testTypesUndefined()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		CircuitFunction cf = new CircuitFunction(tbf);
		gf.add(cf);
		assertNull(gf.getInputType(0));
		assertNull(gf.getInputType(1));
		assertNull(gf.getOutputType(0));
	}
	
	@Test
	public void testReset()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		CircuitFunction cf = new CircuitFunction(tbf);
		CircuitFunctionQueryable cfq = cf.getQueryable();
		assertNull(cfq.m_innerQueryable);
		gf.add(cf);
		gf.associateInput(0, cf, 1);
		gf.associateInput(1, cf, 0);
		gf.associateOutput(0, cf, 0);
		Object[] outputs = new Object[1];
		gf.evaluate(new Object[] {"foo", 2}, outputs);
		assertNotNull(cfq.m_innerQueryable);
		gf.reset();
		assertNull(cfq.m_innerQueryable);
	}
	
	@Test
	public void testConnected()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		CircuitFunction add = new CircuitFunction(Numbers.addition);
		CircuitFunction abs = new CircuitFunction(Numbers.abs);
		gf.add(add, abs);
		gf.connect(add, 0, abs, 0);
		gf.associateInput(0, add, 0);
		gf.associateInput(1, add, 1);
		gf.associateOutput(0, abs, 0);
		Object[] outputs = new Object[1];
		gf.evaluate(new Object[] {-10, 2}, outputs);
		assertEquals(8f, outputs[0]);
	}
	
	@Test
	public void testConnectedDuplicate()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		CircuitFunction add = new CircuitFunction(Numbers.addition);
		CircuitFunction abs = new CircuitFunction(Numbers.abs);
		gf.add(add, abs);
		gf.connect(add, 0, abs, 0);
		gf.associateInput(0, add, 0);
		gf.associateInput(1, add, 1);
		gf.associateOutput(0, abs, 0);
		Object[] outputs = new Object[1];
		gf.evaluate(new Object[] {-10, 2}, outputs);
		assertEquals(8f, outputs[0]);
		GroupFunction gf2 = gf.duplicate();
		gf2.evaluate(new Object[] {-20, 2}, outputs);
		assertEquals(18f, outputs[0]);
	}
	
	@Test
	public void testSubtraction()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		CircuitFunction cf_add = new CircuitFunction(Numbers.subtraction);
		gf.add(cf_add);
		gf.associateInput(0, cf_add, 1);
		gf.associateInput(1, cf_add, 0);
		gf.associateOutput(0, cf_add, 0);
		assertEquals(2, gf.getInputArity());
		assertEquals(1, gf.getOutputArity());
		assertEquals(1, gf.m_innerFunctions.size());
		CircuitFunctionPlaceholder ph1 = gf.m_inputPlaceholders[0];
		assertNotNull(ph1);
		FunctionConnection fc1 = ph1.m_downstreamConnection;
		assertEquals(cf_add, fc1.getObject());
		assertEquals(1, fc1.getIndex());
		CircuitFunctionPlaceholder ph2 = gf.m_inputPlaceholders[1];
		assertNotNull(ph2);
		FunctionConnection fc2 = ph2.m_downstreamConnection;
		assertEquals(cf_add, fc2.getObject());
		assertEquals(0, fc2.getIndex());
		CircuitFunctionPlaceholder ph_dn_1 = gf.m_outputPlaceholders[0];
		FunctionConnection fc_dn = ph_dn_1.m_upstreamConnection;
		assertEquals(cf_add, fc_dn.getObject());
		assertEquals(0, fc_dn.getIndex());
		Object[] outputs = new Object[1];
		Queryable q = gf.evaluate(new Object[] {2, 3}, outputs);
		assertEquals(1f, outputs[0]);
		assertNotNull(q);
	}

	@Test
	public void testDuplicateState()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		CircuitFunction cf_add = new CircuitFunction(Numbers.subtraction);
		gf.add(cf_add);
		gf.associateInput(0, cf_add, 1);
		gf.associateInput(1, cf_add, 0);
		gf.associateOutput(0, cf_add, 0);
		gf.setContext("foo", "bar");
		GroupFunction gf_dup = gf.duplicate(true);
		assertNotNull(gf_dup);
		assertFalse(gf == gf_dup);
		assertFalse(gf.m_innerFunctions == gf_dup.m_innerFunctions);
		assertFalse(gf.m_context == gf_dup.m_context);
		assertEquals("bar", gf_dup.getContext("foo"));
		assertEquals(1, gf_dup.m_innerFunctions.size());
		CircuitFunction cf_dup = null;
		for (CircuitFunction cf : gf_dup.m_innerFunctions)
		{
			assertTrue(cf instanceof CircuitFunction);
			assertFalse(cf == cf_add);
			assertTrue(cf.m_function == cf_add.m_function);
			cf_dup = cf;
			break;
		}
		assertEquals(2, gf_dup.getInputArity());
		assertEquals(1, gf_dup.getOutputArity());
		CircuitFunctionPlaceholder ph1 = gf_dup.m_inputPlaceholders[0];
		assertNotNull(ph1);
		FunctionConnection fc1 = ph1.m_downstreamConnection;
		assertEquals(cf_dup, fc1.getObject());
		assertEquals(1, fc1.getIndex());
		CircuitFunctionPlaceholder ph2 = gf_dup.m_inputPlaceholders[1];
		assertNotNull(ph2);
		FunctionConnection fc2 = ph2.m_downstreamConnection;
		assertEquals(cf_dup, fc2.getObject());
		assertEquals(0, fc2.getIndex());
		CircuitFunctionPlaceholder ph_dn_1 = gf_dup.m_outputPlaceholders[0];
		FunctionConnection fc_dn = ph_dn_1.m_upstreamConnection;
		assertFalse(cf_add == fc_dn.getObject());
		assertEquals(Numbers.subtraction, ((CircuitFunction) fc_dn.getObject()).m_function);
		assertEquals(0, fc_dn.getIndex());
	}

	@Test
	public void testQueryableSubtractionProvenance()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		CircuitFunction cf_add = new CircuitFunction(Numbers.subtraction);
		GroupFunctionQueryable gfq = gf.getQueryable();
		assertNotNull(gfq);
		gf.add(cf_add);
		assertEquals(1, gfq.m_innerQueryables.size());
		CircuitQueryable gfq_cq = null;
		for (CircuitQueryable q : gfq.m_innerQueryables)
		{
			gfq_cq = q;
			break;
		}
		CircuitQueryable add_q = (CircuitQueryable) cf_add.getQueryable();
		assertEquals(gfq_cq, add_q);
		assertNotNull(add_q);
		gf.associateInput(0, cf_add, 1);
		CircuitConnection cc_in_1 = add_q.getInputConnection(1);
		assertNotNull(cc_in_1);
		gf.associateInput(1, cf_add, 0);
		CircuitConnection cc_in_0 = add_q.getInputConnection(0);
		assertNotNull(cc_in_0);
		gf.associateOutput(0, cf_add, 0);
		CircuitConnection cc_out_0 = add_q.getOutputConnection(0);
		assertNotNull(cc_out_0);
		Object[] outputs = new Object[1];
		GroupFunctionQueryable gfq2 = gf.evaluate(new Object[] {2, 3}, outputs);
		assertEquals(1f, outputs[0]);
		assertNotNull(gfq2);
		assertEquals(gfq, gfq2);
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = gfq.query(TraceabilityQuery.ProvenanceQuery.instance, NthOutput.get(0), root, factory);
		assertEquals(2, leaves.size());
		for (TraceabilityNode tn : leaves)
		{
			assertTrue(tn instanceof ObjectNode);
			ObjectNode on = (ObjectNode) tn;
			assertEquals(gfq, on.getDesignatedObject().getObject());
			assertTrue(on.getDesignatedObject().getDesignator().peek() instanceof NthInput);
		}
	}
	
	@Test
	public void testQueryableSubtractionTaint()
	{
		GroupFunction gf = new GroupFunction(2, 1);
		CircuitFunction cf_add = new CircuitFunction(Numbers.subtraction);
		GroupFunctionQueryable gfq = gf.getQueryable();
		assertNotNull(gfq);
		gf.add(cf_add);
		assertEquals(1, gfq.m_innerQueryables.size());
		CircuitQueryable gfq_cq = null;
		for (CircuitQueryable q : gfq.m_innerQueryables)
		{
			gfq_cq = q;
			break;
		}
		CircuitQueryable add_q = (CircuitQueryable) cf_add.getQueryable();
		assertEquals(gfq_cq, add_q);
		assertNotNull(add_q);
		gf.associateInput(0, cf_add, 1);
		CircuitConnection cc_in_1 = add_q.getInputConnection(1);
		assertNotNull(cc_in_1);
		gf.associateInput(1, cf_add, 0);
		CircuitConnection cc_in_0 = add_q.getInputConnection(0);
		assertNotNull(cc_in_0);
		gf.associateOutput(0, cf_add, 0);
		CircuitConnection cc_out_0 = add_q.getOutputConnection(0);
		assertNotNull(cc_out_0);
		Object[] outputs = new Object[1];
		GroupFunctionQueryable gfq2 = gf.evaluate(new Object[] {2, 3}, outputs);
		assertEquals(1f, outputs[0]);
		assertNotNull(gfq2);
		assertEquals(gfq, gfq2);
		ConcreteTracer factory = new ConcreteTracer();
		TraceabilityNode root = factory.getAndNode();
		List<TraceabilityNode> leaves = gfq.query(TraceabilityQuery.TaintQuery.instance, NthInput.get(0), root, factory);
		assertEquals(1, leaves.size());
		for (TraceabilityNode tn : leaves)
		{
			assertTrue(tn instanceof ObjectNode);
			ObjectNode on = (ObjectNode) tn;
			assertEquals(gfq, on.getDesignatedObject().getObject());
			assertTrue(on.getDesignatedObject().getDesignator().peek() instanceof NthOutput);
		}
	}
}
