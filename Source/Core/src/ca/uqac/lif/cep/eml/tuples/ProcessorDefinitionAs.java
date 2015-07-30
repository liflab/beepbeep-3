package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

import ca.uqac.lif.cep.Processor;

public class ProcessorDefinitionAs extends ProcessorDefinition
{
	protected String m_processorName;
	
	protected Processor m_processor;
	
	public ProcessorDefinitionAs()
	{
		super();
	}

	@Override
	public void build(Stack<Object> stack)
	{
		String name = (String) stack.pop();
		Processor proc = (Processor) stack.pop();
		m_processorName = name;
		m_processor = proc;
		stack.push(this);
	}

}
