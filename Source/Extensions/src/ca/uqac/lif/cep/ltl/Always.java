package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.CumulativeProcessor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

/**
 * Troolean implementation of the LTL <b>G</b> operator
 * @author Sylvain Hallé
 */
public class Always extends CumulativeProcessor 
{
	public Always()
	{
		super(new CumulativeFunction<Value>(Troolean.AND_FUNCTION));
	}
}