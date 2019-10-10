package ca.uqac.lif.cep.functions;

import static org.junit.Assert.assertEquals;

import java.util.Map;

import org.junit.Test;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;

public class BinaryFunctionTest 
{
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		TestableBinaryFunction tbf = new TestableBinaryFunction();
		Map<String,Object> printed = (Map<String,Object>) iop.print(tbf);
		assertEquals(2, printed.size());
		
	}
	public static class TestableBinaryFunction extends BinaryFunction<Number,String,Object>
	{
		public TestableBinaryFunction()
		{
			super(Number.class, String.class, Object.class);
		}

		@Override
		public TestableBinaryFunction duplicate(boolean with_state) 
		{
			return new TestableBinaryFunction();
		}

		@Override
		public BinaryFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c)
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException
		{
			// TODO Auto-generated method stub
			return null;
		}
	}
}
