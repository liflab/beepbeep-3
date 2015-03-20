package ca.uqac.lif.cep;

import java.util.Vector;

/**
 * The passthrough processor returns its input as its output
 * @author sylvain
 *
 */
public class Passthrough extends Processor
{
	public Passthrough(int arity)
	{
		super(arity, arity);
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		return inputs;
	}

}
