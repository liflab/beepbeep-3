package ca.uqac.lif.cep.util;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.CumulableFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.SlidableFunction;

public class Numbers 
{
	public static final transient Addition addition = new Addition();
	
	public static final transient Division division = new Division();
	
	private Numbers()
	{
		super();
	}
	
	protected static class Addition implements CumulableFunction<Number>
	{
		protected Addition()
		{
			super();
		}

		@Override
		public int getInputArity() 
		{
			return 2;
		}

		@Override
		public int getOutputArity() 
		{
			return 1;
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			evaluate(inputs, outputs, null);
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			outputs[0] = ((Number) inputs[0]).floatValue() + ((Number) inputs[1]).floatValue();
		}

		@Override
		public Addition duplicate(boolean with_state) 
		{
			return this;
		}

		@Override
		public Addition duplicate() 
		{
			return this;
		}

		@Override
		public Number getInitialValue() 
		{
			return 0;
		}
		
		@Override
		public void reset()
		{
			// Do nothing
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException 
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	protected static class Division implements CumulableFunction<Number>
	{
		protected Division()
		{
			super();
		}

		@Override
		public int getInputArity() 
		{
			return 2;
		}

		@Override
		public int getOutputArity() 
		{
			return 1;
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			evaluate(inputs, outputs, null);
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			outputs[0] = ((Number) inputs[0]).floatValue() + ((Number) inputs[1]).floatValue();
		}

		@Override
		public Division duplicate(boolean with_state) 
		{
			return this;
		}

		@Override
		public Division duplicate() 
		{
			return this;
		}

		@Override
		public Number getInitialValue() 
		{
			return 0;
		}
		
		@Override
		public void reset()
		{
			// Do nothing
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	protected static abstract class SlidableArithmeticFunction implements SlidableFunction
	{
		protected float m_currentValue;
		
		public SlidableArithmeticFunction()
		{
			super();
		}
		
		@Override
		public int getInputArity() 
		{
			return 1;
		}

		@Override
		public int getOutputArity() 
		{
			return 1;
		}
		
		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			evaluate(inputs, outputs,  null);
		}
		
		@Override
		public void devaluate(Object[] inputs, Object[] outputs) 
		{
			devaluate(inputs, outputs,  null);
		}
		
		@Override
		public Function duplicate()
		{
			return duplicate(false);
		}
		
		@Override
		public void reset()
		{
			m_currentValue = 0;
		}
	}
	
	public static class Sum extends SlidableArithmeticFunction
	{
		public Sum()
		{
			super();
		}
		
		@Override
		public void evaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_currentValue += ((Number) inputs[0]).floatValue();
			outputs[0] = m_currentValue;
		}
		
		@Override
		public void devaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_currentValue -= ((Number) inputs[0]).floatValue();
			outputs[0] = m_currentValue;
		}

		@Override
		public Function duplicate(boolean with_state) 
		{
			Sum s = new Sum();
			if (with_state)
			{
				s.m_currentValue = m_currentValue;
			}
			return s;
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	public static class Average extends SlidableArithmeticFunction
	{
		protected int m_numValues;
		
		public Average()
		{
			super();
			m_numValues = 0;
		}
		
		@Override
		public void evaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_currentValue += ((Number) inputs[0]).floatValue();
			m_numValues++;
			outputs[0] = m_currentValue / m_numValues;
			
		}
		
		@Override
		public void devaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_currentValue -= ((Number) inputs[0]).floatValue();
			m_numValues--;
			if (m_numValues > 0)
			{
				outputs[0] = m_currentValue / m_numValues;
			}
			else
			{
				outputs[0] = 0;
			}
		}

		@Override
		public Function duplicate(boolean with_state) 
		{
			Average s = new Average();
			if (with_state)
			{
				s.m_currentValue = m_currentValue;
				s.m_numValues = m_numValues;
			}
			return s;
		}
		
		@Override
		public void reset()
		{
			m_currentValue = 0;
			m_numValues = 0;
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException {
			// TODO Auto-generated method stub
			return null;
		}
	}
}
