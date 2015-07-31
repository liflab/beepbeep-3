package ca.uqac.lif.cep.eml.tuples;

public abstract class ConstantExpression extends AttributeExpression 
{
	@Override
	public AttributeExpression evaluate() 
	{
		return this;
	}
}
