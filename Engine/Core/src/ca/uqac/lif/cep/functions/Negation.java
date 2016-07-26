package ca.uqac.lif.cep.functions;

public class Negation extends UnaryFunction<Boolean,Boolean> 
{
	public static final transient Negation instance = new Negation();
	
	Negation()
	{
		super(Boolean.class, Boolean.class);
	}

	@Override
	public Boolean getValue(Boolean x)
	{
		return !x.booleanValue();
	}
}
