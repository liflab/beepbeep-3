package ca.uqac.lif.cep.ltl;

import java.util.Collection;

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
		if (inputs[0] instanceof Object[])
		{
			for (Object o : (Object[]) inputs[0])
			{
				Value v = Troolean.trooleanValue(o);
				if (v == Value.FALSE)
				{
					out[0] = Value.FALSE;
					return out;
				}
				if (v == Value.INCONCLUSIVE)
				{
					out[0] = Value.INCONCLUSIVE;
					return out;
				}
			}
			out[0] = Value.TRUE;
			return out;
		}
		if (inputs[0] instanceof Collection<?>)
		{
			for (Object o : (Collection<?>) inputs[0])
			{
				Value v = Troolean.trooleanValue(o);
				if (v == Value.FALSE)
				{
					out[0] = Value.FALSE;
					return out;
				}
				if (v == Value.INCONCLUSIVE)
				{
					out[0] = Value.INCONCLUSIVE;
					return out;
				}
			}
			out[0] = Value.TRUE;
			return out;			
		}
		return out;
	}

	@Override
	public Function clone()
	{
		return this;
	}
}