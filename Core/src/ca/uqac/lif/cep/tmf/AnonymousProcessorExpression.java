package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;

import ca.uqac.lif.cep.Processor;

class AnonymousProcessorExpression extends ProcessorExpression
{
	public AnonymousProcessorExpression(Processor p)
	{
		super(p, null);
	}

	public static void build(ArrayDeque<Object> stack)
	{
		Object o;
		Processor p;
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
		AnonymousProcessorExpression te = new AnonymousProcessorExpression(p);
		stack.push(te);
	}
}