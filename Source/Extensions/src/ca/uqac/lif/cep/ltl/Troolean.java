package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.BinaryFunction;
import ca.uqac.lif.cep.UnaryFunction;

public class Troolean 
{
	/**
	 * The three possible values of a Troolean
	 */
	public static enum Value {TRUE, FALSE, INCONCLUSIVE};
	
	/**
	 * Static reference to the And function
	 */
	public static final transient TrooleanAnd AND_FUNCTION = new TrooleanAnd();
	
	/**
	 * Static reference to the Or function
	 */
	public static final transient TrooleanOr OR_FUNCTION = new TrooleanOr();
	
	/**
	 * Static reference to the negation function
	 */
	public static final transient TrooleanNot NOT_FUNCTION = new TrooleanNot();

	/**
	 * Computes the logical conjunction of two Trooleans
	 * @param x The first Troolean
	 * @param y The second Troolean
	 * @return The result
	 */
	public static Value and(Value x, Value y)
	{
		if (x == Value.FALSE || y == Value.FALSE)
		{
			return Value.FALSE;
		}
		if (x == Value.INCONCLUSIVE || y == Value.INCONCLUSIVE)
		{
			return Value.INCONCLUSIVE;
		}
		return Value.TRUE;
	}
	
	/**
	 * Computes the logical conjunction of two Trooleans
	 * @param x The first Troolean
	 * @param y The second Troolean
	 * @return The result
	 */
	public static Value or(Value x, Value y)
	{
		if (x == Value.TRUE || y == Value.TRUE)
		{
			return Value.TRUE;
		}
		if (x == Value.INCONCLUSIVE || y == Value.INCONCLUSIVE)
		{
			return Value.INCONCLUSIVE;
		}
		return Value.FALSE;
	}
	
	/**
	 * Computes the logical negation of a Troolean
	 * @param x The first Troolean
	 * @return The result
	 */
	public static Value not(Value x)
	{
		if (x == Value.FALSE)
		{
			return Value.TRUE;
		}
		if (x == Value.TRUE)
		{
			return Value.FALSE;
		}
		return Value.INCONCLUSIVE;
	}
	
	/**
	 * Converts an ordinary Boolean into a Troolean
	 * @param b The Boolean value
	 * @return The Troolean value
	 */
	public static Value trooleanValue(boolean b)
	{
		if (b == true)
			return Value.TRUE;
		return Value.FALSE;
	}

	/**
	 * Logical conjunction lifted into a binary function
	 */
	public static class TrooleanAnd extends BinaryFunction<Value,Value,Value>
	{
		@Override
		public Value evaluate(Value x, Value y) 
		{
			return and(x, y);
		}
		
		@Override
		public Value getStartValue()
		{
			return Value.TRUE;
		}
		
	}
	
	/**
	 * Logical disjunction lifted into a binary function
	 */
	public static class TrooleanOr extends BinaryFunction<Value,Value,Value>
	{
		@Override
		public Value evaluate(Value x, Value y) 
		{
			return or(x, y);
		}
		
		@Override
		public Value getStartValue()
		{
			return Value.FALSE;
		}
	}
	
	/**
	 * Logical negation lifted into an unary function
	 */
	public static class TrooleanNot extends UnaryFunction<Value,Value>
	{
		@Override
		public Value evaluate(Value x) 
		{
			return not(x);
		}		
	}

}
