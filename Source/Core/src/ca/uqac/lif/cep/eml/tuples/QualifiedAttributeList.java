package ca.uqac.lif.cep.eml.tuples;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import ca.uqac.lif.cep.Buildable;

public class QualifiedAttributeList implements Buildable
{
	protected List<AttributeName> m_attributes;
	
	public QualifiedAttributeList()
	{
		super();
		m_attributes = new LinkedList<AttributeName>();
	}

	@Override
	public void build(Stack<Object> stack)
	{
		Object top = stack.peek();
		if (top instanceof QualifiedAttributeList)
		{
			QualifiedAttributeList qal = (QualifiedAttributeList) stack.pop();
			m_attributes.addAll(qal.m_attributes);
		}
		AttributeName def = (AttributeName) stack.pop();
		m_attributes.add(def);
		stack.push(this);
	}

}
