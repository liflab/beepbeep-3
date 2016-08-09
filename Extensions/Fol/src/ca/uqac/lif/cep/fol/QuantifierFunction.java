package ca.uqac.lif.cep.fol;

import java.util.Set;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.Function;

public abstract class QuantifierFunction extends Function
{
	protected String m_variableName;
	
	protected String m_domainName;
	
	protected Function m_expression;
	
	protected boolean m_stopValue;
	
	public QuantifierFunction(String variable_name, String domain_name, Function expression, boolean stop_value)
	{
		super();
		m_variableName = variable_name;
		m_domainName = domain_name;
		m_expression = expression;
		m_stopValue = stop_value;
	}
	
	@Override
	public Object[] evaluate(Object[] inputs, Context context)
	{
		Interpretation inter = (Interpretation) inputs[0];
		Object[] out = new Object[1];
		Set<Object> values = inter.getDomain(m_domainName);
		int dom_count = 0;
		Context new_context = new Context(context);
		for (Object value : values)
		{
			dom_count++;
			if (m_variableName.compareTo("v") == 0 && dom_count % 1 == 0)
			{
				System.out.println("Dom: " + dom_count);
			}
			new_context.put(m_variableName, value);
			Object[] return_values = m_expression.evaluate(inputs, new_context);
			if (return_values != null && return_values.length > 0 
					&& return_values[0] instanceof Boolean 
					&& (boolean) return_values[0] == m_stopValue)
			{
				out[0] = m_stopValue;
				return out;
			}
		}
		out[0] = !m_stopValue;
		return out;
	}

	@Override
	public Object[] evaluate(Object[] inputs) 
	{
		return evaluate(inputs, new Context());
	}

	@Override
	public int getInputArity() 
	{
		return 1;
	}

	@Override
	public int getOutputArity() 
	{
		return 1;
	}

	@Override
	public void reset() 
	{
		// Nothing to do
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index) 
	{
		classes.add(Interpretation.class);
	}

	@Override
	public Class<?> getOutputTypeFor(int index)
	{
		return Boolean.class;
	}
}
