package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

import ca.uqac.lif.cep.Processor;

public class ProcessorDefinitionPlain extends ProcessorDefinitionAs
{
	public ProcessorDefinitionPlain()
	{
		super();
	}

	@Override
	public void build(Stack<Object> stack)
	{
		Processor proc = (Processor) stack.pop();
		m_processorName = "";
		m_processor = proc;
		stack.push(this);
	}
}
