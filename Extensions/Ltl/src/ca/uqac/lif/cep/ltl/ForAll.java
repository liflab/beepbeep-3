package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.functions.Function;

public class ForAll extends BooleanQuantifier 
{
	ForAll()
	{
		super();
	}
	
	public ForAll(String var_name, Function split_function, Processor p)
	{
		super(var_name, split_function, p, ArrayAnd.instance, Troolean.Value.TRUE);
	}
	
	@Override
	public String toString()
	{
		return "for all " + m_variableName + " in " + m_spawn.m_splitFunction.toString();
	}
	
	@Override
	public ForAll clone() 
	{
		Processor new_proc =  m_spawn.m_processor.clone();
		new_proc.setContext(m_context);
		return new ForAll(m_variableName, m_spawn.m_splitFunction, new_proc);
	}

}
