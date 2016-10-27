package ca.uqac.lif.cep.numbers;

import java.util.Stack;

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
	
	public static void build(Stack<Object> stack) throws ConnectorException
	{
		stack.pop(); // NUMBER
		stack.pop(); // A
		stack.pop(); // INTO
		stack.pop(); // (
		Function left = (Function) stack.pop();
		stack.pop(); // )
		FunctionTree ft = new FunctionTree(instance, left);
		stack.push(ft);
	}
}
