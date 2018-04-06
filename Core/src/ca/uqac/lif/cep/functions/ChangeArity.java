package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.UniformProcessor;

public class ChangeArity extends UniformProcessor
{
	protected Function m_function;
	
	public ChangeArity(int arity, Function f)
	{
		super(arity, f.getOutputArity());
		m_function = f;
	}

	@Override
	public ChangeArity duplicate(boolean with_state) 
	{
		return new ChangeArity(getInputArity(), m_function.duplicate(with_state));
	}

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs)
	{
		m_function.evaluate(inputs, outputs, m_context);
		return true;
	}
}
