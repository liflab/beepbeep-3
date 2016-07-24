package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.functions.Function;

public class Exists extends BooleanQuantifier 
{
	Exists()
	{
		super();
	}
	
	public Exists(String var_name, Function split_function, Processor p)
	{
		super(var_name, split_function, p, ArrayOr.instance, Troolean.Value.FALSE);
	}
	
	@Override
	public String toString()
	{
		return "exists " + m_variableName + " in " + m_spawn.m_splitFunction.toString();
	}
	
	@Override
	public Exists clone() 
	{
		Processor new_proc =  m_spawn.m_processor.clone();
		new_proc.setContext(m_context);
		return new Exists(m_variableName, m_spawn.m_splitFunction, new_proc);
	}

}
