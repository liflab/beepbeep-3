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
package ca.uqac.lif.cep.util;

import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * A container object for functions applying to numbers.
 * @author Sylvain Hallé
 *
 */
public class Numbers
{
	protected Numbers()
	{
		// Utility class
	}
	
	/**
	 * Computes the absolute value of its argument
	 */
	public static final AbsoluteValue absoluteValue = new AbsoluteValue();
	
	/**
	 * Adds two numbers
	 */
	public static final Addition addition = new Addition();
	
	/**
	 * Computes the quotient of two numbers
	 */
	public static final Division division = new Division();
	
	public static final IsEven isEven = new IsEven();
	
	public static final IsGreaterOrEqual isGreaterOrEqual = new IsGreaterOrEqual();
	
	public static final IsGreaterThan isGreaterThan = new IsGreaterThan();
	
	public static final IsLessOrEqual isLessOrEqual = new IsLessOrEqual();
	
	public static final IsLessThan isLessThan = new IsLessThan();
	
	public static final Maximum maximum = new Maximum();
	
	public static final Minimum minimum = new Minimum();
	
	public static final Multiplication multiplication = new Multiplication();
	
	public static final NumberCast numberCast = new NumberCast();
	
	public static final Power power = new Power();
	
	public static final Signum signum = new Signum();
	
	public static final SquareRoot squareRoot = new SquareRoot();
	
	public static final Subtraction subtraction = new Subtraction();
	
	/**
	 * Computes the absolute value of its argument
	 * @author Sylvain Hallé
	 */
	public static final class AbsoluteValue extends UnaryFunction<Number,Number>
	{
		protected AbsoluteValue()
		{
			super(Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x)
		{
			return Math.abs(x.floatValue());
		}

		@Override
		public String toString()
		{
			return "ABS";
		}
	}
	
	/**
	 * Computes the sum of its arguments
	 * @author Sylvain Hallé
	 */
	public static final class Addition extends BinaryFunction<Number,Number,Number>
	{
		/**
		 * Make constructor private, to force users to refer to the static
		 * instance of addition
		 */
		protected Addition()
		{
			super(Number.class, Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x, Number y)
		{
			return x.floatValue() + y.floatValue();
		}

		@Override
		public Number getStartValue()
		{
			return 0f;
		}

		@Override
		public String toString()
		{
			return "+";
		}
	}

	/**
	 * Computes the quotient of its arguments
	 * @author Sylvain Hallé
	 */
	public static final class Division extends BinaryFunction<Number,Number,Number>
	{
		protected  Division()
		{
			super(Number.class, Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x, Number y)
		{
			return x.floatValue() / y.floatValue();
		}

		@Override
		public Number getStartValue()
		{
			return 1f;
		}

		@Override
		public String toString()
		{
			return "÷";
		}
	}

	/**
	 * Computes if a number is even
	 * @author Sylvain Hallé
	 */
	public static final class IsEven extends UnaryFunction<Number,Boolean>
	{
		protected  IsEven()
		{
			super(Number.class, Boolean.class);
		}

		@Override
		public Boolean getValue(Number x)
		{
			if (x.floatValue() != Math.round(x.floatValue()))
			{
				// Not an integer
				return false;
			}
			return x.intValue() % 2 == 0;
		}

		@Override
		public String toString()
		{
			return "IS EVEN";
		}
	}

	public static final class IsGreaterOrEqual extends BinaryFunction<Number,Number,Boolean>
	{
		protected  IsGreaterOrEqual()
		{
			super(Number.class, Number.class, Boolean.class);
		}

		@Override
		public Boolean getValue(Number x, Number y)
		{
			return x.floatValue() >= y.floatValue();
		}

		@Override
		public Boolean getStartValue()
		{
			return false;
		}

		@Override
		public String toString()
		{
			return "≥";
		}

	}

	public static final class IsGreaterThan extends BinaryFunction<Number,Number,Boolean>
	{
		protected  IsGreaterThan()
		{
			super(Number.class, Number.class, Boolean.class);
		}

		@Override
		public Boolean getValue(Number x, Number y)
		{
			return x.floatValue() > y.floatValue();
		}

		@Override
		public Boolean getStartValue()
		{
			return false;
		}

		@Override
		public String toString()
		{
			return ">";
		}

	}
	
	public static final class IsLessOrEqual extends BinaryFunction<Number,Number,Boolean>
	{
		private IsLessOrEqual()
		{
			super(Number.class, Number.class, Boolean.class);
		}

		@Override
		public Boolean getValue(Number x, Number y)
		{
			return x.floatValue() <= y.floatValue();
		}

		@Override
		public Boolean getStartValue()
		{
			return false;
		}

		@Override
		public String toString()
		{
			return "≤";
		}

	}
	
	public static final class IsLessThan extends BinaryFunction<Number,Number,Boolean>
	{
		protected IsLessThan()
		{
			super(Number.class, Number.class, Boolean.class);
		}

		@Override
		public Boolean getValue(Number x, Number y)
		{
			return x.floatValue() < y.floatValue();
		}

		@Override
		public Boolean getStartValue()
		{
			return false;
		}

		@Override
		public String toString()
		{
			return "<";
		}

	}

	/**
	 * Returns the maximum of two numbers.
	 * @author Sylvain Hallé
	 */
	public static final class Maximum extends BinaryFunction<Number,Number,Number>
	{
		protected Maximum()
		{
			super(Number.class, Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x, Number y) 
		{
			return Math.max(x.floatValue(), y.floatValue());
		}
		
		@Override
		public Number getStartValue()
		{
			return Float.MIN_VALUE;
		}

	}

	/**
	 * Returns the minimum of two numbers.
	 * @author Sylvain Hallé
	 */
	public static final class Minimum extends BinaryFunction<Number,Number,Number>
	{
		protected Minimum()
		{
			super(Number.class, Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x, Number y) 
		{
			return Math.min(x.floatValue(), y.floatValue());
		}
		
		@Override
		public Number getStartValue()
		{
			return Float.MAX_VALUE;
		}

	}

	/**
	 * Computes the product of its arguments
	 * @author Sylvain Hallé
	 */
	public static final class Multiplication extends BinaryFunction<Number,Number,Number>
	{
		protected Multiplication()
		{
			super(Number.class, Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x, Number y)
		{
			return x.floatValue() * y.floatValue();
		}

		@Override
		public Number getStartValue()
		{
			return 1f;
		}

		@Override
		public String toString()
		{
			return "×";
		}

	}

	/**
	 * Converts an object into a number
	 * @author Sylvain Hallé
	 */
	public static final class NumberCast extends UnaryFunction<Object,Number>
	{
		protected NumberCast()
		{
			super(Object.class, Number.class);
		}

		@Override
		public Number getValue(Object x)
		{
			return getNumber(x);
		}

		@Override
		public NumberCast duplicate()
		{
			return this;
		}

		/**
		 * Converts an object into a number
		 * @param x The object
		 * @return A number
		 */
		public static final Number getNumber(Object x)
		{
			if (x instanceof Number)
			{
				return (Number) x;
			}
			if (x instanceof String)
			{
				try
				{
					return Integer.parseInt((String) x);
				}
				catch (NumberFormatException e)
				{
					try
					{
						return Float.parseFloat((String) x);
					}
					catch (NumberFormatException e2)
					{
						throw new FunctionException(e2);
					}
				}
			}
			throw new FunctionException("Object incompatible with Number");
		}
	}

	/**
	 * Computes the power of its arguments
	 * @author Sylvain Hallé
	 */
	public static final class Power extends BinaryFunction<Number,Number,Number>
	{
		protected Power()
		{
			super(Number.class, Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x, Number y)
		{
			return Math.pow(x.floatValue(), y.floatValue());
		}

		@Override
		public Number getStartValue()
		{
			return 1f;
		}
	}

	/**
	 * Computes the signum of its argument
	 * @author Sylvain Hallé
	 */
	public static final class Signum extends UnaryFunction<Number,Number>
	{
		protected Signum()
		{
			super(Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x)
		{
			if (x.floatValue() < 0)
			{
				return -1;
			}
			if (x.floatValue() > 0)
			{
				return 1;
			}
			return 0;
		}

		@Override
		public String toString()
		{
			return "SIG";
		}
	}

	/**
	 * Computes the square root of its argument
	 * @author Sylvain Hallé
	 */
	public static final class SquareRoot extends UnaryFunction<Number,Number>
	{
		protected SquareRoot()
		{
			super(Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x)
		{
			return Math.sqrt(x.floatValue());
		}

		@Override
		public String toString()
		{
			return "√";
		}

	}
	
	/**
	 * Computes the difference of its arguments
	 * @author Sylvain Hallé
	 */
	public static final class Subtraction extends BinaryFunction<Number,Number,Number>
	{
		private Subtraction()
		{
			super(Number.class, Number.class, Number.class);
		}

		@Override
		public Number getValue(Number x, Number y)
		{
			return x.floatValue() - y.floatValue();
		}

		@Override
		public Number getStartValue()
		{
			return 0f;
		}

		@Override
		public String toString()
		{
			return "-";
		}

	}
}
