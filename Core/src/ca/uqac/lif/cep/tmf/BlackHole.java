package ca.uqac.lif.cep.tmf;

import java.util.List;
import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.Trackable;

public class BlackHole extends Sink
{
	public BlackHole(int in_arity)
	{
		super(in_arity);
		m_queryable = new ProcessorQueryable(toString(), in_arity, 0);
	}
	
	public BlackHole()
	{
		this(1);
	}
	
	@Override
	public Processor duplicate(boolean with_state) 
	{
		BlackHole bh = new BlackHole(getInputArity());
		return copyInto(bh, with_state);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) 
	{
		return false;
	}

	@Override
	protected SingleProcessor readState(Object state, int in_arity, int out_arity) throws ReadException 
	{
		return new BlackHole(in_arity);
	}

	@Override
	protected Object printState() 
	{
		return null;
	}

}
