package ca.uqac.lif.cep.tuples;

import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.util.CacheMap;

public final class AttributePlaceholder extends AttributeName
{
	private static final AttributePlaceholder s_instance = new AttributePlaceholder();
	
	@Override
	public Object evaluate(CacheMap<Object> inputs)
	{
		Object only_value = inputs.getValue(0);
		return only_value;
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException
	{
		stack.pop(); // *
		stack.push(s_instance);
	}
}
