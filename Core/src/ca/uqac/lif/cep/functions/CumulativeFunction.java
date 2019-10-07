package ca.uqac.lif.cep.functions;

import java.util.ArrayList;
import java.util.List;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Context;

public class CumulativeFunction<T> implements Function
{
	protected T m_currentValue;
	
	/*@ non_null @*/ protected CumulableFunction<T> m_function;
	
	public CumulativeFunction(/*@ non_null @*/ CumulableFunction<T> f)
	{
		super();
		m_function = f;
		m_currentValue = f.getInitialValue();
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
	public final void evaluate(Object[] inputs, Object[] outputs) 
	{
		evaluate(inputs, outputs, null);
	}

	@SuppressWarnings("unchecked")
	@Override
	public void evaluate(Object[] inputs, Object[] outputs, Context context) 
	{
		Object[] ins = new Object[] {m_currentValue, inputs[0]};
		m_function.evaluate(ins, outputs, context);
		m_currentValue = (T) outputs[0];
	}

	@SuppressWarnings("unchecked")
	@Override
	public CumulativeFunction<T> duplicate(boolean with_state)
	{
		CumulativeFunction<T> new_f = new CumulativeFunction<T>((CumulableFunction<T>) m_function.duplicate(with_state));
		if (with_state)
		{
			new_f.m_currentValue = m_currentValue;
		}
		return new_f;
	}

	@Override
	public Function duplicate() 
	{
		return duplicate(true);
	}
	
	public void reset()
	{
		m_currentValue = m_function.getInitialValue();
	}

	@Override
	public Object print(ObjectPrinter<?> printer) throws PrintException
	{
		List<Object> list = new ArrayList<Object>(2);
		list.add(m_function);
		list.add(m_currentValue);
		return printer.print(list);
	}

	@SuppressWarnings("unchecked")
	@Override
	public Object read(ObjectReader<?> reader, Object o) throws ReadException
	{
		Object state = reader.read(o);
		if (!(state instanceof List))
		{
			throw new ReadException("Unexpected object");
		}
		List<?> list = (List<?>) state;
		if (list.size() != 2)
		{
			throw new ReadException("Invalid list format");
		}
		Object o_f = list.get(0);
		if (!(o_f instanceof CumulableFunction))
		{
			throw new ReadException("Unexpected object");
		}
		try
		{
			CumulativeFunction<T> cf = new CumulativeFunction<T>((CumulableFunction<T>) o_f);
			cf.m_currentValue = (T) list.get(1);
			return cf;
		}
		catch (ClassCastException e)
		{
			throw new ReadException(e);
		}
	}
}
