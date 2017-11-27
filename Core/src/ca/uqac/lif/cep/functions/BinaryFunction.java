package ca.uqac.lif.cep.functions;

import java.util.Set;

/**
 * Function of two inputs and one output
 * @param <T> The type of the first input
 * @param <V> The type of the second input
 * @param <U> The type of the output
 */
public abstract class BinaryFunction<T,V,U> extends Function
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
	public void evaluate(/*@NonNull*/ Object[] inputs, Object[] outputs)
	{
		outputs[0] = getValue((T) inputs[0], (V) inputs[1]);
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
	public BinaryFunction<T,V,U> duplicate()
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

}
