package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.ltl.Troolean.Value;
import ca.uqac.lif.cep.ltl.TrooleanQuantifier.ArrayTroolean;

public class ArrayAnd extends ArrayTroolean
{
	public static final transient ArrayAnd instance = new ArrayAnd();
	
	@Override
	public Value[] compute(Object[] inputs)
	{
		Value[] out = new Value[1];
		Object[] val_array = (Object[]) inputs[0];
		out[0] = Troolean.and(Troolean.trooleanValues(val_array));
		return out;
	}

	@Override
	public Function clone()
	{
		return this;
	}
}