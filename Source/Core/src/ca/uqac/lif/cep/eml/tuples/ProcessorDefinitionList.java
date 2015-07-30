package ca.uqac.lif.cep.eml.tuples;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import ca.uqac.lif.cep.Buildable;

public class ProcessorDefinitionList implements Buildable
{
	List<ProcessorDefinition> m_definitions;
	
	public ProcessorDefinitionList()
	{
		super();
		m_definitions = new LinkedList<ProcessorDefinition>();
	}

	@Override
	public void build(Stack<Object> stack)
	{
		Object top = stack.peek();
		if (top instanceof ProcessorDefinitionList)
		{
			ProcessorDefinitionList pdl = (ProcessorDefinitionList) stack.pop();
			m_definitions.addAll(pdl.m_definitions);
		}
		ProcessorDefinition def = (ProcessorDefinition) stack.pop();
		m_definitions.add(def);
		stack.push(this);
	}

}
