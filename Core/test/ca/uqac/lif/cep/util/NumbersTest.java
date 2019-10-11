package ca.uqac.lif.cep.util;

import static org.junit.Assert.*;

import java.util.List;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.cep.functions.BinaryFunction.BinaryFunctionQueryable;
import ca.uqac.lif.cep.functions.BinaryFunction.BinaryFunctionQueryable.Inputs;
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
	public void testAdditionPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		assertNull(iop.print(Numbers.addition));
	}
	
	@Test
	public void testAdditionRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Object o = Numbers.addition.read(ior, null);
		assertEquals(Numbers.addition, o);
	}
	
	@Test
	public void testAdditionDuplicate()
	{
		assertEquals(Numbers.addition, Numbers.addition.duplicate());
	}
	
	@Test
	public void testAdditionValues()
	{
		Object[] outputs = new Object[1];
		Numbers.addition.evaluate(new Object[] {3, 2}, outputs);
		assertEquals(5f, outputs[0]);
		assertEquals(0, Numbers.addition.getInitialValue());
	}
	
	@Test
	public void testSubtractionValues()
	{
		Object[] outputs = new Object[1];
		Numbers.subtraction.evaluate(new Object[] {3, 2}, outputs);
		assertEquals(1f, outputs[0]);
		assertEquals(0, Numbers.subtraction.getInitialValue());
	}
	
	@Test
	public void testSubtractionPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		assertNull(iop.print(Numbers.subtraction));
	}
	
	@Test
	public void testSubtractionRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Object o = Numbers.subtraction.read(ior, null);
		assertEquals(Numbers.subtraction, o);
	}
	
	@Test
	public void testSubtractionDuplicate()
	{
		assertEquals(Numbers.subtraction, Numbers.subtraction.duplicate());
	}
	
	@Test
	public void testMultiplicationValues()
	{
		Object[] outputs = new Object[1];
		Numbers.multiplication.evaluate(new Object[] {3, 2}, outputs);
		assertEquals(6f, outputs[0]);
		assertEquals(1, Numbers.multiplication.getInitialValue());
	}
	
	@Test
	public void testMultiplicationQueryableProvenance1()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {3, 2}, outputs);
		assertEquals(Inputs.BOTH, bfq.getInputDependency());
	}
	
	@Test
	public void testMultiplicationPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		assertNull(iop.print(Numbers.multiplication));
	}
	
	@Test
	public void testMultiplicationRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Object o = Numbers.multiplication.read(ior, null);
		assertEquals(Numbers.multiplication, o);
	}
	
	@Test
	public void testMultiplicationDuplicate()
	{
		assertEquals(Numbers.multiplication, Numbers.multiplication.duplicate());
	}
	
	@Test
	public void testMultiplicationQueryableCausality1()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {3, 2}, outputs);
		assertEquals(Inputs.BOTH, bfq.getInputDependency());
	}
	
	@Test
	public void testMultiplicationQueryableCausality2()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {0, 2}, outputs);
		assertEquals(Inputs.LEFT, bfq.getInputDependency());
	}
	
	@Test
	public void testMultiplicationQueryableCausality3()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {2, 0}, outputs);
		assertEquals(Inputs.RIGHT, bfq.getInputDependency());
	}
	
	@Test
	public void testMultiplicationQueryableCausality4()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.multiplication.evaluate(new Object[] {0, 0}, outputs);
		assertEquals(Inputs.ANY, bfq.getInputDependency());
	}
	
	@Test
	public void testDivisionValues()
	{
		Object[] outputs = new Object[1];
		Numbers.division.evaluate(new Object[] {3, 2}, outputs);
		assertEquals(1.5f, outputs[0]);
		assertEquals(1, Numbers.division.getInitialValue());
	}
	
	@Test
	public void testDivisionPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		assertNull(iop.print(Numbers.division));
	}
	
	@Test
	public void testDivisionRead() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		Object o = Numbers.division.read(ior, null);
		assertEquals(Numbers.division, o);
	}
	
	@Test
	public void testDivisionDuplicate()
	{
		assertEquals(Numbers.division, Numbers.division.duplicate());
	}
	
	@Test
	public void testDivisionQueryableCausality1()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.division.evaluate(new Object[] {3, 2}, outputs);
		assertEquals(Inputs.BOTH, bfq.getInputDependency());
	}
	
	@Test
	public void testDivisionQueryableCausality2()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.division.evaluate(new Object[] {0, 2}, outputs);
		assertEquals(Inputs.LEFT, bfq.getInputDependency());
	}
	
	@Test
	public void testDivisionQueryableCausality3()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.division.evaluate(new Object[] {2, 0}, outputs);
		assertEquals(Inputs.RIGHT, bfq.getInputDependency());
	}
	
	@Test
	public void testDivisionQueryableCausality4()
	{
		Object[] outputs = new Object[1];
		BinaryFunctionQueryable bfq = Numbers.division.evaluate(new Object[] {0, 0}, outputs);
		assertEquals(Inputs.BOTH, bfq.getInputDependency());
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
