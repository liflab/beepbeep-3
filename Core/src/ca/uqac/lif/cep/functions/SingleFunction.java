package ca.uqac.lif.cep.functions;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;

public abstract class SingleFunction implements Function
{
	protected FunctionQueryable m_queryable;
	
	/*@ non_null @*/ protected CircuitConnection[] m_inputConnections;
	
	/*@ non_null @*/ protected CircuitConnection[] m_outputConnections;
	
	/*@ non_null @*/ protected Object[] m_outputValues;
	
	/*@ non_null @*/ protected Context m_context;
	
	protected boolean m_computed;
	
	public SingleFunction(int in_arity, int out_arity)
	{
		super();
		m_inputConnections = new CircuitConnection[in_arity];
		m_outputConnections = new CircuitConnection[out_arity];
		m_outputValues = new Object[out_arity];
		m_computed = false;
		m_context = new Context();
	}
	
	@Override
	public final FunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c)
	{
		m_queryable = computeValue(inputs, outputs, c);
		m_computed = true;
		return m_queryable;
	}
	
	@Override
	public final FunctionQueryable evaluate(Object[] inputs, Object[] outputs) 
	{
		return evaluate(inputs, outputs, m_context);
	}
	
	@Override
	public final Queryable getQueryable()
	{
		return m_queryable;
	}
	
	@Override
	public final int getInputArity()
	{
		return m_inputConnections.length;
	}
	
	@Override
	public final int getOutputArity()
	{
		return m_outputConnections.length;
	}
	
	@Override
	public void setToInput(int index, CircuitConnection conn)
	{
		try
		{
			m_inputConnections[index] = conn;
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	@Override
	public void setToOutput(int index, CircuitConnection conn)
	{
		try
		{
			m_outputConnections[index] = conn;
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	@Override
	public CircuitConnection getInputConnection(int index)
	{
		try
		{
			return m_inputConnections[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	@Override
	public CircuitConnection getOutputConnection(int index)
	{
		try
		{
			return m_outputConnections[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	@Override
	public final Object getOutput()
	{
		return getOutput(0);
	}
	
	public final Object getOutput(int index)
	{
		if (!m_computed)
		{
			Object[] inputs = new Object[m_inputConnections.length];
			for (int i = 0; i < m_inputConnections.length; i++)
			{
				CircuitConnection cc = m_inputConnections[i];
				Function f = (Function) cc.getObject();
				inputs[i] = f.getOutput(cc.getIndex());
			}
			evaluate(inputs, m_outputValues, m_context); 
		}
		try
		{
			return m_outputValues[index];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new FunctionException(e);
		}
	}
	
	@Override
	public void reset()
	{
		m_computed = false;
	}
	
	@Override
	public Object getContext(String key)
	{
		if (!m_context.containsKey(key))
		{
			return null;
		}
		return m_context.get(key);
	}

	@Override
	public void setContext(String key, Object value)
	{
		m_context.put(key, value);
	}
	
	@Override
	public final SingleFunction duplicate()
	{
		return (SingleFunction) duplicate(false);
	}
	
	@Override
	public final Object print(ObjectPrinter<?> printer) throws PrintException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public final Object read(ObjectReader<?> reader, Object o) throws ReadException {
		// TODO Auto-generated method stub
		return null;
	}
	
	public abstract Object printState();
	
	public abstract SingleFunction readState(int in_arity, int out_arity, Object o);
	
	protected abstract FunctionQueryable computeValue(Object[] inputs, Object[] outputs, Context c);
}
