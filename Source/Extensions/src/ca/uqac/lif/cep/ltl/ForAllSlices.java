package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.Function;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class ForAllSlices extends FirstOrderSlicer
{
	public ForAllSlices(Function slice_function, Processor p) 
	{
		super(slice_function, p);
	}

	@Override
	protected CumulativeFunction<Value> getMergeFunction()
	{
		return new CumulativeFunction<Value>(Troolean.AND_FUNCTION);
	}
}
