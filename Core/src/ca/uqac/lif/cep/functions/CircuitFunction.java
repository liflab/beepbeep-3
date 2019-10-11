package ca.uqac.lif.cep.functions;

import java.util.HashMap;
import java.util.Map;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Contextualizable;
import ca.uqac.lif.cep.StateDuplicable;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.Trackable;
import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;
import ca.uqac.lif.petitpoucet.circuit.CircuitElement;

public class CircuitFunction implements CircuitElement, Contextualizable, Function, Outputable, Trackable
{
	/*@ non_null @*/ protected CircuitConnection[] m_inputConnections;
	
	/*@ non_null @*/ protected CircuitConnection[] m_outputConnections;
	
	/*@ non_null @*/ protected Object[] m_outputValues;
	
	/*@ non_null @*/ protected Context m_context;
	
	/*@ non_null @*/ protected Function m_function;
	
	protected Queryable m_queryable;
	
	protected boolean m_computed;
	
	public static final transient String s_functionKey = "function";
	
	public static final transient String s_contentsKey = "contents";
	
	public static final transient String s_queryableKey = "queryable";
	
	public CircuitFunction(/*@ non_null @*/ Function f)
	{
		super();
		m_function = f;
		m_inputConnections = new CircuitConnection[f.getInputArity()];
		m_outputConnections = new CircuitConnection[f.getOutputArity()];
		m_outputValues = new Object[f.getOutputArity()];
		m_computed = false;
		m_context = new Context();
		m_queryable = null;
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
	public final CircuitConnection getInputConnection(int index)
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
	public final CircuitConnection getOutputConnection(int index)
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
				Outputable f = (Outputable) cc.getObject();
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
	public final CircuitFunction duplicate()
	{
		return (CircuitFunction) duplicate(false);
	}
	
	@Override
	public CircuitFunction duplicate(boolean with_state)
	{
		CircuitFunction cf = new CircuitFunction(m_function.duplicate(with_state));
		return copyInto(cf, with_state);
	}
	
	@SuppressWarnings("unchecked")
	protected CircuitFunction copyInto(/*@ non_null @*/ CircuitFunction cf, boolean with_state)
	{
		if (with_state)
		{
			cf.m_context.putAll(m_context);
			if (m_queryable != null && m_queryable instanceof StateDuplicable<?>)
			{
				cf.m_queryable = ((StateDuplicable<Queryable>) m_queryable).duplicate(with_state);
			}
			for (int i = 0; i < m_outputValues.length; i++)
			{
				cf.m_outputValues[i] = m_outputValues[i];
			}
		}
		return cf;
	}
	
	@Override
	public final Map<String,Object> print(ObjectPrinter<?> printer) throws PrintException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put(s_functionKey, m_function);
		map.put(s_queryableKey, m_queryable);
		Object contents = printState();
		if (contents != null)
		{
			map.put(s_contentsKey, contents);
		}
		return map;
	}
	
	protected Object printState()
	{
		return null;
	}
	
	protected CircuitFunction readState(Function f, Object o)
	{
		return new CircuitFunction(f);
	}

	@SuppressWarnings("unchecked")
	@Override
	public final Object read(ObjectReader<?> reader, Object o) throws ReadException 
	{
		Object r_o = reader.read(o);
		if (r_o == null || !(r_o instanceof Map))
		{
			throw new ReadException("Unexpected serialized object format");
		}
		try
		{
			Map<String,Object> map = (Map<String,Object>) r_o;
			if (!map.containsKey(s_functionKey) || !map.containsKey(s_queryableKey))
			{
				throw new ReadException("Unexpected map format");
			}
			Function f = (Function) map.get(s_functionKey);
			FunctionQueryable fq = (FunctionQueryable) map.get(s_queryableKey);
			Object contents = null;
			if (map.containsKey(s_contentsKey))
			{
				contents = map.get(s_contentsKey);
			}
			CircuitFunction cf = readState(f, contents);
			cf.m_queryable = fq;
			return cf;
		}
		catch (ClassCastException e)
		{
			throw new ReadException(e);
		}
	}
	
	@Override
	public final Queryable evaluate(Object[] inputs, Object[] outputs, Context c)
	{
		m_queryable = m_function.evaluate(inputs, outputs, c);
		m_computed = true;
		return m_queryable;
	}
	
	@Override
	public final Queryable evaluate(Object[] inputs, Object[] outputs) 
	{
		return evaluate(inputs, outputs, m_context);
	}

	@Override
	public Class<?> getInputType(int index)
	{
		return m_function.getInputType(index);
	}

	@Override
	public Class<?> getOutputType(int index) 
	{
		return m_function.getOutputType(index);
	}
}
