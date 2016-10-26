package ca.uqac.lif.cep.tmf;

import java.util.ArrayList;
import java.util.Stack;

/**
 * A list of input traces. This class exists only to provide
 * an object to build when parsing an expression.
 * 
 * @author Sylvain Hallé
 */
public class ProcessorExpressionList extends ArrayList<ProcessorExpression>
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;

	public static void build(Stack<Object> stack)
	{
		Object top = stack.peek();
		ProcessorExpressionList new_al = new ProcessorExpressionList();
		if (top instanceof ProcessorExpressionList)
		{
			ProcessorExpressionList al = (ProcessorExpressionList) stack.pop();
			stack.pop(); // ,
			ProcessorExpression def = (ProcessorExpression) stack.pop();
			new_al.add(def);
			new_al.addAll(al);
		}
		else
		{
			ProcessorExpression def = (ProcessorExpression) stack.pop();
			new_al.add(def);
		}
		stack.push(new_al);
	}

	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		boolean first = true;
		for (ProcessorExpression te : this)
		{
			if (first)
			{
				first = false;
			}
			else
			{
				out.append(", ");
			}
			out.append(te);
		}
		return out.toString();
	}
}