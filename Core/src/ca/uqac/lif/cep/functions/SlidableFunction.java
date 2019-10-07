package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.Context;

public interface SlidableFunction extends Function
{
	public void devaluate(Object[] inputs, Object[] outputs, Context context);
	
	public void devaluate(Object[] inputs, Object[] outputs);
}
