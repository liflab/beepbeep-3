package ca.uqac.lif.cep;

/**
 * Function of two inputs and one output
 * @param <T> The type of the first input
 * @param <V> The type of the second input
 * @param <U> The type of the output
 */
public abstract class BinaryFunction<T,V,U> implements Function 
{
	@SuppressWarnings("unchecked")
	@Override
	/*@ requires inputs.length == 2 */
	public /*@NonNull*/ Object[] compute(/*@NonNull*/ Object[] inputs) 
	{
		Object[] out = new Object[1];
		out[0] = evaluate((T) inputs[0], (V) inputs[1]);
		return out;
	}
	
	/**
	 * Evaluates the function
	 * @param x The first argument
	 * @param y The second argument
	 * @return The return value of the function
	 */
	public abstract U evaluate(T x, V y); 

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
}
