package ca.uqac.lif.cep.epl;

import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;

public class Switch extends SingleProcessor
{
	public Switch(int in_arity)
	{
		super(in_arity, 1);
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs) 
	{
		System.out.print(m_uniqueId);
		for (Object o : inputs)
		{
			System.out.print(", " + o);
		}
		System.out.println();
		for (int i = 0; i < inputs.length; i+= 2)
		{
			if ((boolean) inputs[i])
			{
				return wrapObject(inputs[i+1]);
			}
		}
		return null;
	}

	@Override
	public Switch clone() 
	{
		return new Switch(getInputArity());
	}
	
}
