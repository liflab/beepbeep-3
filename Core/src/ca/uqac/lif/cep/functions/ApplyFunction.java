package ca.uqac.lif.cep.functions;

import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.petitpoucet.functions.Function;
import ca.uqac.lif.petitpoucet.functions.Function.FunctionException;

public class ApplyFunction extends SingleProcessor
{
	/*@ non_null @*/ protected Function m_function;
	
	public ApplyFunction(/*@ non_null @*/ Function f)
	{
		super(f.getInputArity(), f.getOutputArity());
		m_function = f;
	}
	
	@Override
	public Processor duplicate(boolean with_state) 
	{
		ApplyFunction af = new ApplyFunction(m_function.duplicate(with_state));
		return copyInto(af, with_state);
	}

	@Override
	public boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		Object[] out = new Object[] {m_function.getOutputArity()};
		try
		{
			m_function.evaluate(inputs, out, m_context);
		}
		catch (FunctionException e)
		{
			throw new ProcessorException(e);
		}
		outputs.add(out);
		return true;
	}
	
	@Override
	protected Object printState()
	{
		return m_function;
	}

	@Override
	protected SingleProcessor readState(Object state, int in_arity, int out_arity) throws ReadException
	{
		if (!(state instanceof Function))
		{
			throw new ReadException("Unexpected object");
		}
		return new ApplyFunction((Function) state);
	}
}
