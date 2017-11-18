package ca.uqac.lif.cep.sets;

import java.util.Collection;
import java.util.HashMap;

import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.UnaryFunction;

@SuppressWarnings("rawtypes")
public class MapValues extends UnaryFunction<HashMap,Multiset>
{
	public static final transient MapValues instance = new MapValues();
	
	MapValues() 
	{
		super(HashMap.class, Multiset.class);
	}

	@Override
	public Multiset getValue(HashMap x) throws FunctionException 
	{
		Collection<?> values = x.values();
		Multiset set = new Multiset();
		set.addAll(values);
		return set;
	}
}
