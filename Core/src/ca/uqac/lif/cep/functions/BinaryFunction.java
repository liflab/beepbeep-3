package ca.uqac.lif.cep.functions;

import java.util.Set;
import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;

/**
 * Function of two inputs and one output
 * @param <T> The type of the first input
 * @param <V> The type of the second input
 * @param <U> The type of the output
 */
public abstract class BinaryFunction<T,V,U> extends SimpleFunction
{
	/**
	 * The class of the first input
	 */
	private Class<T> m_inputTypeLeft;

	/**
	 * The class of the second input
	 */
	private Class<V> m_inputTypeRight;

	/**
	 * The class of the output
	 */
	private Class<U> m_outputType;

	/**
	 * Creates a new instance of a binary function
	 * @param t The class of the first input
	 * @param v The class of the second input
	 * @param u The class of the output
	 */
	public BinaryFunction(Class<T> t, Class<V> v, Class<U> u)
	{
		super();
		m_inputTypeLeft = t;
		m_inputTypeRight = v;
		m_outputType = u;
	}

	@SuppressWarnings("unchecked")
	@Override
	/*@ requires inputs.length == 2 */
	public /*@NonNull*/ Object[] compute(/*@NonNull*/ Object[] inputs)
	{
		Object[] out = new Object[1];
		out[0] = getValue((T) inputs[0], (V) inputs[1]);
		return out;
	}

	/**
	 * Evaluates the function
	 * @param x The first argument
	 * @param y The second argument
	 * @return The return value of the function
	 */
	public abstract U getValue(T x, V y);

	@Override
	public final int getInputArity()
	{
		return 2;
	}

	@Override
	public final int getOutputArity()
	{
		return 1;
	}

	/**
	 * Gets a reasonable starting value if this function is used to
	 * create a {@link CumulativeFunction}. You only need to override
	 * this method if the function is expected to be used in a cumulative
	 * function; otherwise returning null is fine.
	 * @return A start value
	 */
	public U getStartValue()
	{
		return null;
	}

	@Override
	public void reset()
	{
		// Do nothing
	}

	@Override
	public BinaryFunction<T,V,U> clone()
	{
		return this;
	}

	public final Class<T> getInputTypeLeft()
	{
		return m_inputTypeLeft;
	}

	public final Class<V> getInputTypeRight()
	{
		return m_inputTypeRight;
	}

	@Override
	public final void getInputTypesFor(/*@NotNull*/ Set<Class<?>> classes, int index)
	{
		if (index == 0)
		{
			classes.add(m_inputTypeLeft);
		}
		else
		{
			classes.add(m_inputTypeRight);
		}
	}

	public final Class<U> getOutputType()
	{
		return m_outputType;
	}

	@Override
	public final Class<?> getOutputTypeFor(int index)
	{
		return m_outputType;
	}

	/**
	 * Builds a binary infix function from a parse stack
	 * @param stack The parse stack
	 * @param instance The instance of binary function to build
	 * @throws ConnectorException
	 */
	public static void buildInfix(Stack<Object> stack, BinaryFunction<?,?,?> instance) throws ConnectorException
	{
		// We take care of the fact that either of the arguments
		// can be surrounded by parentheses or not
		Object o;
		Function left, right;
		o = stack.pop(); // ) ?
		if (o instanceof String)
		{
			right = (Function) stack.pop();
			stack.pop(); // (
		}
		else
		{
			right = (Function) o;
		}
		stack.pop(); // symbol
		o = stack.pop(); // ) ?
		if (o instanceof String)
		{
			left = (Function) stack.pop();
			stack.pop(); // (
		}
		else
		{
			left = (Function) o;
		}
		FunctionTree ft = new FunctionTree(instance, left, right);
		stack.push(ft);
	}

}
