package ca.uqac.lif.cep.functions;

import java.util.Stack;

public class ConstantProcessor extends FunctionProcessor 
{
	public ConstantProcessor(Constant comp)
	{
		super(comp);
	}
	
	public static void build(Stack<Object> stack)
	{
		stack.pop(); // (
		Constant o = (Constant) stack.pop();
		stack.pop(); // )
		stack.pop(); // CONSTANT
		FunctionProcessor fp = new FunctionProcessor(o);
		stack.push(fp);
	}

}
