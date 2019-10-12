package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.Context;

public abstract class UnaryFunction<T,V> implements Function
{
	/*@ non_null @*/ protected Class<? extends T> m_inputType;
	
	/*@ non_null @*/ protected Class<? extends V> m_outputType;
	
	public UnaryFunction(Class<? extends T> t_input, Class<? extends V> t_output)
	{
		super();
		m_inputType = t_input;
		m_outputType = t_output;
	}
	
	@Override
	public final int getInputArity()
	{
		return 1;
	}
	
	@Override
	public final int getOutputArity()
	{
		return 1;
	}
	
	@Override
	public Class<? extends V> getOutputType(int index)
	{
		return m_outputType;
	}
	
	@Override
	public Class<?> getInputType(int index)
	{
		if (index == 0)
		{
			return m_inputType;
		}
		return null;
	}
	
	@Override
	public final FunctionQueryable evaluate(Object[] inputs, Object[] outputs) 
	{
		return evaluate(inputs, outputs, null);
	}
	
	@Override
	public void reset()
	{
		// Nothing to do
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public UnaryFunction<T,V> duplicate() 
	{
		return (UnaryFunction<T,V>) duplicate(false);
	}
	
	@Override
	public abstract FunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c);
}
