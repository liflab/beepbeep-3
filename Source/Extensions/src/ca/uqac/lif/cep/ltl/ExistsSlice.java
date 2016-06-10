package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.Function;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class ExistsSlice extends FirstOrderSlicer
{
	public ExistsSlice(Function slice_function, Processor p) 
	{
		super(slice_function, p);
	}

	@Override
	protected CumulativeFunction<Value> getMergeFunction()
	{
		return new Sometime();
	}
}