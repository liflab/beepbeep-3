package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class Sometime extends CumulativeFunction<Value> 
{
	public Sometime()
	{
		super(Troolean.OR_FUNCTION);
	}
}