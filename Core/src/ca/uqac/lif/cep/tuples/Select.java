package ca.uqac.lif.cep.tuples;

import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.FunctionProcessor;

public class Select extends FunctionProcessor
{
	public Select(SelectFunction function)
	{
		super(function);
	}
	
	public Select(int in_arity)
	{
		super(new SelectFunction(in_arity));
	}
	
	public Select(int in_arity, String ... attributes)
	{
		super(new SelectFunction(in_arity, attributes));
	}
	
	public Select(int in_arity, AttributeExpression ... expressions)
	{
		super(new SelectFunction(in_arity, expressions));
	}
	
	public Select(int in_arity, AttributeDefinition... definitions)
	{
		super(new SelectFunction(in_arity, definitions));
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException
	{
		stack.pop(); // (
		ProcessorDefinitionList pdl = (ProcessorDefinitionList) stack.pop();
		stack.pop(); // )
		stack.pop(); // FROM
		AttributeList al = (AttributeList) stack.pop();
		stack.pop(); // SELECT
		Select sel = new Select(pdl.size());
		((SelectFunction) sel.m_function).m_processors = pdl;
		// Connect each processor to the input
		int j = 0;
		for (ProcessorDefinition pd : pdl)
		{
			Connector.connect(pd.m_processor, sel, 0, j);
			j++;
		}
		((SelectFunction) sel.m_function).m_attributeList = al;
		stack.push(sel);
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_function.reset();
	}
	
	@Override
	public Select clone()
	{
		return new Select((SelectFunction) m_function.clone(m_context));
	}
	
	@Override
	public void setContext(Context context)
	{
		super.setContext(context);
		m_function.setContext(context);
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		super.setContext(key, value);
		m_function.setContext(key, value);
	}
}
