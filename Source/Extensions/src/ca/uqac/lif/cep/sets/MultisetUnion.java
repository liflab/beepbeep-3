package ca.uqac.lif.cep.sets;

import ca.uqac.lif.cep.BinaryFunction;

public class MultisetUnion extends BinaryFunction<Multiset,Multiset,Multiset> 
{
	@Override
	public Multiset evaluate(Multiset x, Multiset y) 
	{
		return x.addAll(y);
	}

	@Override
	public Multiset getStartValue() 
	{
		return new Multiset();
	}
}
