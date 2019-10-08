package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.SingleProcessor;

public abstract class Sink extends SingleProcessor
{
	public Sink(int in_arity)
	{
		super(in_arity, 0);
	}
}
