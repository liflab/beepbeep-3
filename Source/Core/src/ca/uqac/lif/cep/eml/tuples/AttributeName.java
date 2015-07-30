package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

import ca.uqac.lif.cep.Buildable;

public class AttributeName implements Buildable
{
	protected String m_name;
	
	public AttributeName()
	{
		super();
	}

	@Override
	public void build(Stack<Object> stack)
	{
		m_name = (String) stack.pop();
		stack.push(this);
	}

}
