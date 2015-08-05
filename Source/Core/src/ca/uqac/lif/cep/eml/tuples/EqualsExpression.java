package ca.uqac.lif.cep.eml.tuples;

import java.util.Map;

public class EqualsExpression extends BinaryExpression 
{
	public EqualsExpression()
	{
		super();
		m_symbol = "=";
	}

	@Override
	public EmlConstant evaluate(Map<String, Tuple> inputs) 
	{
		EmlConstant left = m_left.evaluate(inputs);
		EmlConstant right = m_right.evaluate(inputs);
		if (left != null && right != null && left.equals(right))
		{
			return new EmlBoolean(true);
		}
		return new EmlBoolean(false);
	}

}
