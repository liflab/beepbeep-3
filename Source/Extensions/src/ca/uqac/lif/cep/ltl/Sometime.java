package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.CumulativeProcessor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

/**
 * Troolean implementation of the LTL <b>F</b> processor
 * @author Sylvain Hallé
 */
public class Sometime extends CumulativeProcessor 
{
	public Sometime()
	{
		super(new CumulativeFunction<Value>(Troolean.OR_FUNCTION));
	}
}