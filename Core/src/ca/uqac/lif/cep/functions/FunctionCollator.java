package ca.uqac.lif.cep.functions;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.tmf.Collator;

public class FunctionCollator extends SingleProcessor 
{
	protected Function m_function;
	
	public FunctionCollator(Function f)
	{
		super(1, f.getOutputArity());
		m_function = f;
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException, ConnectorException
	{
		Collator col = (Collator) stack.pop();
		stack.pop(); // )
		Function f = (Function) stack.pop();
		stack.pop(); // (
		stack.pop(); // APPLY
		FunctionCollator fp = new FunctionCollator(f);
		Connector.connect(col, fp);
		/*int i = 0;
		for (ProcessorExpression pe : col.getProcessorList())
		{
			Connector.connect(pe.getProcessor(), 0, fp, i);
			i++;
		}*/
		stack.push(fp);
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object[] outputs = m_function.evaluate(inputs);
		return wrapVector(outputs);
	}

	@Override
	public Processor clone()
	{
		return new FunctionCollator(m_function.clone(getContext()));
	}
}
