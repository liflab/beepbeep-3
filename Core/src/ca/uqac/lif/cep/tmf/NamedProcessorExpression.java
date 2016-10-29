package ca.uqac.lif.cep.tmf;

import java.util.Stack;

import ca.uqac.lif.cep.Processor;

class NamedProcessorExpression extends ProcessorExpression
{
	public NamedProcessorExpression(Processor p, String n) 
	{
		super(p, n);
	}

	public static void build(Stack<Object> stack)
	{
		Object o;
		Processor p;
		String name = (String) stack.pop();
		stack.pop(); // AS
		o = stack.pop(); // ( ?
		if (o instanceof String)
		{
			p = (Processor) stack.pop();
			stack.pop(); // )
		}
		else
		{
			p = (Processor) o;
		}
		NamedProcessorExpression te = new NamedProcessorExpression(p, name);
		stack.push(te);
	}
}