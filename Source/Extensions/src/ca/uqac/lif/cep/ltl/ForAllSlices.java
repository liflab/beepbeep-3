package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.Function;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.epl.Slicer;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class ForAllSlices extends Slicer 
{
	public ForAllSlices(Function slice_function, Processor p) 
	{
		super(slice_function, p);
	}
}
