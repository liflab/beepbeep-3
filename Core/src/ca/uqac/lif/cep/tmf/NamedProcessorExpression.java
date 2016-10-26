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
		String name = (String) stack.pop();
		stack.pop(); // AS
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		NamedProcessorExpression te = new NamedProcessorExpression(p, name);
		stack.push(te);
	}
}