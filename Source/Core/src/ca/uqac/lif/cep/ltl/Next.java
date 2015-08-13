package ca.uqac.lif.cep.ltl;

import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Delay;
import ca.uqac.lif.cep.Processor;

public class Next extends Delay
{
	public Next()
	{
		super(1);
	}
	
	@Override
	public void build(Stack<Object> stack) 
	{
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // X
		Connector.connect(p,  this);
		stack.push(this);
	}
	
	@Override
	public Next newInstance()
	{
		return new Next();
	}

}
