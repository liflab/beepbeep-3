package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class Always extends CumulativeFunction<Value> 
{
	public Always()
	{
		super(Troolean.AND_FUNCTION);
	}
}