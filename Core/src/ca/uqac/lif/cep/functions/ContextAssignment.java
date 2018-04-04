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
	 * Gets the name of the context element to modify
	 * @return The variable
	 */
	public String getVariable()
	{
		return m_lvalue;
	}
	
	/**
	 * Gets the function computing the value to assign to the context element.
	 * @return The function
	 */
	public Function getAssignment()
	{
		return m_value;
	}

	/**
	 * Assigns a value to a context element
	 * @param inputs The inputs to evaluate the assignment function
	 * @param context The context to update
	 * @ Any exception occurring when assigning a value
	 *   to the context element
	 */
	public void assign(Object[] inputs, Object[] outputs, Context context) 
	{
		m_value.evaluate(inputs, outputs, context);
		context.put(m_lvalue, outputs[0]);
	}

	/**
	 * Updates the context of an object
	 * @param inputs The inputs to evaluate the assignment function
	 * @param c The object
	 * @ Any exception occurring when assigning a value
	 *   to the context element
	 */
	public void assign(Object[] inputs, Object[] outputs, Contextualizable c) 
	{
		Context context = c.getContext();
		assign(inputs, outputs, context);
		c.setContext(context);
	}

	@Override
	public String toString()
	{
		return m_lvalue + ":=" + m_value;
	}
}
