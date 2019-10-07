package ca.uqac.lif.cep.tmf;

import java.util.List;
import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.Trackable;

public class Fork extends SingleProcessor
{
	public Fork(int arity)
	{
		super(1, arity);
	}
	
	public Fork()
	{
		this(2);
	}

	@Override
	public Processor duplicate(boolean with_state)
	{
		Fork pt = new Fork(getOutputArity());
		return copyInto(pt, with_state);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
	{
		Object[] out = new Object[getOutputArity()];
		for (int i = 0; i < out.length; i++)
		{
			out[i] = inputs[0];
		}
		outputs.add(out);
		return true;
	}

	@Override
	protected SingleProcessor readState(Object state, int in_arity, int out_arity) throws ReadException
	{
		return new Fork(out_arity);
	}

	@Override
	protected Object printState() 
	{
		return null;
	}
}
