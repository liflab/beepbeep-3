package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

public class EmlPlainString extends EmlString
{
	public static void build(Stack<Object> stack)
	{
		Object o = stack.pop();
		if (o instanceof String)
		{
			stack.push(new EmlString((String) o));
		}
		else if (o instanceof Number)
		{
			stack.push(new EmlString(o.toString()));
		}
	}
}
