package ca.uqac.lif.cep.fol;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.Function;

public class ExistsFunction extends QuantifierFunction
{
	public ExistsFunction(String variable_name, String domain_name, Function expression)
	{
		super(variable_name, domain_name, expression, true);
	}

	@Override
	public ExistsFunction clone() 
	{
		return new ExistsFunction(m_variableName, m_domainName, m_expression.clone());
	}
	
	@Override
	public ExistsFunction clone(Context context) 
	{
		return new ExistsFunction(m_variableName, m_domainName, m_expression.clone(context));
	}
	
	@Override
	public String toString()
	{
		return "exists " + m_variableName + " in " + m_domainName + " : " + m_expression;
	}

}
