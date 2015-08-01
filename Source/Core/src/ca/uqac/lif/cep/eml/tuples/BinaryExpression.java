package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

public abstract class BinaryExpression extends AttributeExpression
{
	protected AttributeExpression m_left;
	
	protected AttributeExpression m_right;
	
	protected String m_symbol;

	@Override
	public void build(Stack<Object> stack)
	{
		stack.pop(); // )
		AttributeExpression exp_right = (AttributeExpression) stack.pop();
		stack.pop(); // (
		m_symbol = (String) stack.pop(); // The symbol
		stack.pop(); // )
		AttributeExpression exp_left = (AttributeExpression) stack.pop();
		stack.pop(); // (
		m_left = exp_left;
		m_right = exp_right;
		stack.push(this);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("(").append(m_left).append(") ").append(m_symbol).append(" (").append(m_right).append(")");
		return out.toString();
	}
}
