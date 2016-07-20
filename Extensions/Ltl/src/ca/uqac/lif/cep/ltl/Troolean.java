/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Implementation of a three-valued logic. The "Troolean" type
 * has three values: TRUE, FALSE and INCONCLUSIVE (which can also
 * stand for UNKNOWN).
 */
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
	 * Computes the logical conjunction of two values
	 * @param x The first value
	 * @param y The second value
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
	
	public static Value and(Value[] values)
	{
		for (Value v : values)
		{
			if (v == Value.FALSE)
			{
				return Value.FALSE;
			}
			if (v == Value.INCONCLUSIVE)
			{
				return Value.INCONCLUSIVE;
			}
		}
		return Value.TRUE;
	}
	
	public static Value or(Value[] values)
	{
		for (Value v : values)
		{
			if (v == Value.TRUE)
			{
				return Value.TRUE;
			}
			if (v == Value.INCONCLUSIVE)
			{
				return Value.INCONCLUSIVE;
			}
		}
		return Value.FALSE;
	}

	
	/**
	 * Computes the logical conjunction of two values
	 * @param a The first value
	 * @param b The second value
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
	 * Computes the logical negation of a value
	 * @param a The first value
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
	 * Converts an object into a Troolean. The method uses the following
	 * rules:
	 * <ul>
	 * <li><tt>null</tt> evaluates to INCONCLUSIVE</li>
	 * <li>Ordinary Booleans evaluate to their corresponding value</li>
	 * <li>Ordinary Trooleans evaluate to their corresponding value</li>
	 * <li>The strings "1", "true" and "T" evaluate to TRUE</li>
	 * <li>The strings "0", "false" and "F" evaluate to FALSE</li> 
	 * <li>All other strings evaluate to INCONCLUSIVE</li>
	 * <li>All other objects evaluate to INCONCLUSIVE</li>
	 * </ul>
	 * @param b The object
	 * @return The Troolean value
	 */
	public static Value trooleanValue(Object o)
	{
		if (o == null)
		{
			return Value.INCONCLUSIVE;
		}
		if (o instanceof Value)
		{
			return (Value) o;
		}
		if (o instanceof Boolean)
		{
			if (((Boolean) o).booleanValue() == true)
			{
				return Value.TRUE;
			}
			return Value.FALSE;
		}
		if (o instanceof String)
		{
			String s = (String) o;
			if (s.compareTo("1") == 0 || 
					s.compareToIgnoreCase("true") == 0 || 
					s.compareToIgnoreCase("T") == 0)
			{
				return Value.TRUE;
			}
			if (s.compareTo("0") == 0 || 
					s.compareToIgnoreCase("false") == 0 || 
					s.compareToIgnoreCase("F") == 0)
			{
				return Value.FALSE;
			}
			else
			{
				return Value.INCONCLUSIVE;
			}
		}
		return Value.INCONCLUSIVE;
	}

	/**
	 * Logical conjunction lifted into a binary function
	 */
	private static class TrooleanAnd extends BinaryFunction<Value,Value,Value>
	{
		TrooleanAnd()
		{
			super(Value.class, Value.class, Value.class);
		}
		
		@Override
		public Value getValue(Value x, Value y) 
		{
			return and(x, y);
		}
		
		@Override
		public Value getStartValue()
		{
			return Value.INCONCLUSIVE;
		}
		
	}
	
	/**
	 * Logical disjunction lifted into a binary function
	 */
	private static class TrooleanOr extends BinaryFunction<Value,Value,Value>
	{
		TrooleanOr()
		{
			super(Value.class, Value.class, Value.class);
		}
		
		@Override
		public Value getValue(Value x, Value y) 
		{
			return or(x, y);
		}
		
		@Override
		public Value getStartValue()
		{
			return Value.INCONCLUSIVE;
		}
	}
	
	/**
	 * Logical negation lifted into an unary function
	 */
	private static class TrooleanNot extends UnaryFunction<Value,Value>
	{
		TrooleanNot()
		{
			super(Value.class, Value.class);
		}
		
		@Override
		public Value getValue(Value x) 
		{
			return not(x);
		}		
	}

}
