package ca.uqac.lif.cep.numbers;

import java.util.ArrayDeque;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.functions.UnaryFunction;

public class NumberCast extends UnaryFunction<Object,Number>
{
	public static final transient NumberCast instance = new NumberCast();

	NumberCast()
	{
		super(Object.class, Number.class);
	}

	@Override
	public Number getValue(Object x)
	{
		return getNumber(x);
	}

	@Override
	public NumberCast clone()
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

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		Object o;
		Function left;
		stack.pop(); // NUMBER
		stack.pop(); // A
		stack.pop(); // INTO
		o = stack.pop(); // ( ?
		if (o instanceof String)
		{
			left = (Function) stack.pop();
			stack.pop(); // )
		}
		else
		{
			left = (Function) o;
		}
		stack.pop(); // TURN
		FunctionTree ft = new FunctionTree(instance, left);
		stack.push(ft);
	}
}
