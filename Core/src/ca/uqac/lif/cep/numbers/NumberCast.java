package ca.uqac.lif.cep.numbers;

import ca.uqac.lif.cep.functions.UnaryFunction;

public class NumberCast extends UnaryFunction<Object,Number>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -7200217647590938462L;
	public static final transient NumberCast instance = new NumberCast();

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

	public static Number getNumber(Object x)
	{
		if (x instanceof Number)
		{
			return (Number) x;
		}
		if (x instanceof String)
		{
			try
			{
				return Float.parseFloat((String) x);
			}
			catch (NumberFormatException e)
			{
				return 0;
			}
		}
		return 0;
	}
}
