package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

public abstract class EmlPlainString extends EmlString
{
	public static void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		if (o instanceof String)
		{
			stack.push((String) o);
		}
		else if (o instanceof Number)
		{
			stack.push(o.toString());
		}
	}
}
