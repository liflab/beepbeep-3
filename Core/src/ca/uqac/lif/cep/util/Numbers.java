package ca.uqac.lif.cep.util;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.BinaryFunction.BinaryFunctionQueryable.Inputs;
import ca.uqac.lif.cep.functions.CumulableFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.SlidableFunction;

public class Numbers 
{
	public static final transient Addition addition = new Addition();
	
	public static final transient Subtraction subtraction = new Subtraction();
	
	public static final transient Multiplication multiplication = new Multiplication();
	
	public static final transient Division division = new Division();
	
	private Numbers()
	{
		super();
	}
	
	protected static class Addition extends BinaryFunction<Number,Number,Number> implements CumulableFunction<Number>
	{
		protected Addition()
		{
			super(Number.class, Number.class, Number.class);
		}
		
		@Override
		public BinaryFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c) 
		{
			outputs[0] = ((Number) inputs[0]).floatValue() + ((Number) inputs[1]).floatValue();
			return new BinaryFunctionQueryable(toString(), Inputs.BOTH);
		}

		@Override
		public Addition duplicate(boolean with_state) 
		{
			return this;
		}

		@Override
		public Number getInitialValue() 
		{
			return 0;
		}
		
		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException 
		{
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException
		{
			return this;
		}
	}
	
	protected static class Subtraction extends BinaryFunction<Number,Number,Number> implements CumulableFunction<Number>
	{
		protected Subtraction()
		{
			super(Number.class, Number.class, Number.class);
		}
		
		@Override
		public BinaryFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c) 
		{
			outputs[0] = ((Number) inputs[0]).floatValue() - ((Number) inputs[1]).floatValue();
			return new BinaryFunctionQueryable(toString(), Inputs.BOTH);
		}

		@Override
		public Subtraction duplicate(boolean with_state) 
		{
			return this;
		}

		@Override
		public Number getInitialValue() 
		{
			return 0;
		}
		
		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException 
		{
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException
		{
			return this;
		}
	}
	
	protected static class Multiplication extends BinaryFunction<Number,Number,Number> implements CumulableFunction<Number>
	{
		protected Multiplication()
		{
			super(Number.class, Number.class, Number.class);
		}
		
		@Override
		public BinaryFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c) 
		{
			outputs[0] = ((Number) inputs[0]).floatValue() * ((Number) inputs[1]).floatValue();
			return new BinaryFunctionQueryable(toString(), getDependency(((Number) inputs[0]).floatValue(), ((Number) inputs[1]).floatValue()));
		}

		@Override
		public Multiplication duplicate(boolean with_state) 
		{
			return this;
		}

		@Override
		public Number getInitialValue() 
		{
			return 1;
		}
		
		protected static Inputs getDependency(float x, float y)
		{
			if (x == 0)
			{
				if (y == 0)
				{
					return Inputs.ANY;
				}
				return Inputs.LEFT;
			}
			if (y == 0)
			{
				return Inputs.RIGHT;
			}
			return Inputs.BOTH;
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException 
		{
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException
		{
			return this;
		}
	}
	
	protected static class Division extends BinaryFunction<Number,Number,Number> implements CumulableFunction<Number>
	{
		protected Division()
		{
			super(Number.class, Number.class, Number.class);
		}
		
		@Override
		public BinaryFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c) 
		{
			outputs[0] = ((Number) inputs[0]).floatValue() / ((Number) inputs[1]).floatValue();
			return new BinaryFunctionQueryable(toString(), getDependency(((Number) inputs[0]).floatValue(), ((Number) inputs[1]).floatValue()));
		}

		@Override
		public Division duplicate(boolean with_state) 
		{
			return this;
		}

		@Override
		public Number getInitialValue() 
		{
			return 1;
		}
		
		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException 
		{
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException
		{
			return this;
		}
		
		protected static Inputs getDependency(float x, float y)
		{
			if (x == 0)
			{
				if (y == 0)
				{
					// Undefined 0/0
					return Inputs.BOTH;
				}
				return Inputs.LEFT;
			}
			if (y == 0)
			{
				// Division by 0
				return Inputs.RIGHT;
			}
			return Inputs.BOTH;
		}
	}
	
	protected static abstract class SlidableArithmeticFunction implements SlidableFunction
	{
		protected float m_currentValue;
		
		protected SlidableFunctionQueryable m_queryable;
		
		public SlidableArithmeticFunction()
		{
			super();
			m_queryable = new SlidableFunctionQueryable(toString());
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
		public Class<?> getInputType(int index)
		{
			if (index == 0) 
			{
				return Number.class;
			}
			return null;
		}
		
		@Override
		public Class<?> getOutputType(int index)
		{
			return Number.class;
		}
		
		@Override
		public SlidableFunctionQueryable evaluate(Object[] inputs, Object[] outputs) 
		{
			return evaluate(inputs, outputs,  null);
		}
		
		@Override
		public SlidableFunctionQueryable devaluate(Object[] inputs, Object[] outputs) 
		{
			return devaluate(inputs, outputs,  null);
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
			m_queryable.reset();
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
	
	public static class Sum extends SlidableArithmeticFunction
	{
		public Sum()
		{
			super();
		}
		
		@Override
		public SlidableFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_currentValue += ((Number) inputs[0]).floatValue();
			outputs[0] = m_currentValue;
			m_queryable.addCallToEvaluate();
			return m_queryable;
		}
		
		@Override
		public SlidableFunctionQueryable devaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_currentValue -= ((Number) inputs[0]).floatValue();
			outputs[0] = m_currentValue;
			m_queryable.addCallToDevaluate();
			return m_queryable;
		}

		@Override
		public Sum duplicate(boolean with_state) 
		{
			Sum s = new Sum();
			if (with_state)
			{
				s.m_currentValue = m_currentValue;
			}
			return s;
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
		public SlidableFunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_currentValue += ((Number) inputs[0]).floatValue();
			m_numValues++;
			outputs[0] = m_currentValue / m_numValues;
			m_queryable.addCallToEvaluate();
			return m_queryable;
			
		}
		
		@Override
		public SlidableFunctionQueryable devaluate(Object[] inputs, Object[] outputs, Context context) 
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
			m_queryable.addCallToDevaluate();
			return m_queryable;
		}

		@Override
		public Average duplicate(boolean with_state) 
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
			super.reset();
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
