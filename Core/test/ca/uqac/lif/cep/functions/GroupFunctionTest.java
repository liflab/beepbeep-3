package ca.uqac.lif.cep.functions;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import ca.uqac.lif.cep.functions.FunctionConnector.FunctionConnection;
import ca.uqac.lif.cep.functions.GroupFunction.CircuitFunctionPlaceholder;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.petitpoucet.Queryable;

public class GroupFunctionTest 
{
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
		GroupFunction gf_dup = gf.duplicate(true);
		assertNotNull(gf_dup);
		assertFalse(gf == gf_dup);
		assertFalse(gf.m_innerFunctions == gf_dup.m_innerFunctions);
		assertFalse(gf.m_context == gf_dup.m_context);
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
}
