package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Contextualizable;

public class ContextAssignment 
{
	/**
	 * The name of the context element to modify
	 */
	protected String m_lvalue;
	
	/**
	 * The function computing the value to assign to the context element.
	 * It is assumed that this function has an output arity of 1.
	 */
	protected Function m_value;
	
	public ContextAssignment(String left, Function right)
	{
		super();
		m_lvalue = left;
		m_value = right;
	}
	
	/**
	 * Assigns a value to a context element
	 * @param inputs The inputs to evaluate the assignment function
	 * @param context The context to update
	 */
	public void assign(Object[] inputs, Context context)
	{
		Object[] v = m_value.evaluate(inputs, context);
		context.put(m_lvalue, v[0]);
	}
	
	/**
	 * Updates the context of an object
	 * @param inputs The inputs to evaluate the assignment function
	 * @param c The object
	 */
	public void assign(Object[] inputs, Contextualizable c)
	{
		Context context = c.getContext();
		assign(inputs, context);
		c.setContext(context);
	}
	
	@Override
	public String toString()
	{
		return m_lvalue + ":=" + m_value;
	}
}
