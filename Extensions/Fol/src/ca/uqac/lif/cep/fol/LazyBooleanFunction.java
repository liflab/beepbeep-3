package ca.uqac.lif.cep.fol;

import java.util.Set;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.functions.Negation;
import ca.uqac.lif.cep.functions.UnaryFunction;


public class LazyBooleanFunction extends Function
{
	protected boolean m_stopValue;
	
	protected Function m_left;
	
	protected Function m_right;
	
	public LazyBooleanFunction(boolean stop_value, Function left, Function right)
	{
		super();
		m_left = left;
		m_right = right;
		m_stopValue = stop_value;
	}
	
	@Override
	public int getInputArity()
	{
		// 1, since we take as input an interpretation
		return 1;
	}
	
	@Override
	public int getOutputArity()
	{
		return 1;
	}
	
	@Override
	public Object[] evaluate(Object[] inputs, Context context)
	{
		Object[] out = new Object[1];
		// Evaluate LHS
		boolean value = (boolean) m_left.evaluate(inputs, context)[0];
		if (value == m_stopValue)
		{
			out[0] = m_stopValue;
			return out;
		}
		// Evaluate RHS
		value = (boolean) m_right.evaluate(inputs, context)[0];
		if (value == m_stopValue)
		{
			out[0] = m_stopValue;
			return out;				
		}
		out[0] = !m_stopValue;
		return out;
	}
	
	@Override
	public Object[] evaluate(Object[] inputs)
	{
		return evaluate(inputs, null);
	}
	
	protected static class DummyInterpretationFunction extends UnaryFunction<Interpretation,Boolean>
	{
		public static final transient DummyInterpretationFunction instance = new DummyInterpretationFunction();
		
		DummyInterpretationFunction()
		{
			super(Interpretation.class, Boolean.class);
		}

		@Override
		public Boolean getValue(Interpretation x)
		{
			return true;
		}
		
		@Override
		public DummyInterpretationFunction clone()
		{
			return this;
		}
	}
	
	public static class And extends LazyBooleanFunction
	{
		public And(Function left, Function right)
		{
			super(false, left, right);
		}
		
		@Override
		public String toString()
		{
			return "(" + m_left + " and " + m_right + ")";
		}
		
		@Override
		public And clone(Context context)
		{
			return new And(m_left.clone(context), m_right.clone(context));
		}
		
		@Override
		public And clone()
		{
			return clone(null);
		}

	}
	
	public static class Or extends LazyBooleanFunction
	{
		public Or(Function left, Function right)
		{
			super(true, left, right);
		}
		
		@Override
		public String toString()
		{
			return "(" + m_left + " or " + m_right + ")";
		}
		
		@Override
		public Or clone(Context context)
		{
			return new Or(m_left.clone(context), m_right.clone(context));
		}
		
		@Override
		public Or clone()
		{
			return clone(null);
		}
	}
	
	public static class Implies extends LazyBooleanFunction
	{
		public Implies(Function left, Function right)
		{
			super(true, new FunctionTree(Negation.instance, left), right);
		}
		
		@Override
		public String toString()
		{
			return "(" + m_left + " implies " + m_right + ")";
		}
		
		@Override
		public Implies clone(Context context)
		{
			return new Implies(m_left.clone(context), m_right.clone(context));
		}
		
		@Override
		public Implies clone()
		{
			return clone(null);
		}

	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public Function clone() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public Class<?> getOutputTypeFor(int index) {
		// TODO Auto-generated method stub
		return null;
	}
}
