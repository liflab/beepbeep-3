package ca.uqac.lif.cep.tuples;

import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;

public abstract class EmlPlainString extends EmlString
{
	public static void build(Stack<Object> stack) throws ConnectorException
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
