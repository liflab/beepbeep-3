package ca.uqac.lif.cep.concurrency;

import java.util.Set;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.concurrency.ThreadManager.ManagedThread;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionException;

public class NonBlockingFunction extends Function implements Runnable
{
	protected Function m_function;
	
	protected ThreadManager m_manager;
	
	protected ManagedThread m_thread;
	
	protected Object[] m_inputs;
	
	protected Object[] m_outputs;
	
	protected Context m_context;
	
	public NonBlockingFunction(Function f, ThreadManager manager)
	{
		super();
		m_function = f;
		m_manager = manager;
		m_thread = null;
	}
	
	public void evaluate(Object[] inputs, Object[] outputs, Context context) throws FunctionException
	{
		m_function.evaluate(inputs, outputs, context);
	}
	
	public void evaluateFast(Object[] inputs, Object[] outputs, Context context)
	{
		m_inputs = inputs;
		m_outputs = outputs;
		m_context = context;
		m_thread = m_manager.tryNewThread(this);
		if (m_thread != null)
		{
			m_thread.start();
		}
		else
		{
			// No new thread, so call run() in this thread
			run();
		}
	}
	
	public void waitFor()
	{
		if (m_thread == null)
		{
			return;
		}
		while (m_thread.isAlive())
		{
			try 
			{
				Thread.sleep(0);
			} 
			catch (InterruptedException e)
			{
				// Do nothing
			}
		}
	}

	@Override
	public void run() 
	{
		try
		{
			m_function.evaluate(m_inputs, m_outputs, m_context);
		}
		catch (FunctionException e)
		{
			// TODO: auto-generated catch block
		}
		if (m_thread != null)
		{
			m_thread.dispose();
		}
	}

	@Override
	public void evaluate(Object[] inputs, Object[] outputs) throws FunctionException 
	{
		m_function.evaluate(inputs, outputs);
		if (m_thread != null)
		{
			m_thread.dispose();
		}
	}
	
	@Override
	public int getInputArity() 
	{
		return m_function.getInputArity();
	}

	@Override
	public int getOutputArity()
	{
		return m_function.getOutputArity();
	}

	@Override
	public void reset() 
	{
		m_function.reset();
		
	}

	@Override
	public Function clone()
	{
		return new NonBlockingFunction(m_function.clone(), m_manager);
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index)
	{
		m_function.getInputTypesFor(classes, index);
	}

	@Override
	public Class<?> getOutputTypeFor(int index)
	{
		return m_function.getOutputTypeFor(index);
	}
}
