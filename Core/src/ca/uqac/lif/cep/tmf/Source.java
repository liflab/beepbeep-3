package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;
import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;

public abstract class Source extends SingleProcessor
{
	public Source(int out_arity)
	{
		super(0, out_arity);
	}
}
