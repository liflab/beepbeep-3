package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Duplicable;

public interface DuplicableFunction extends Duplicable
{
	@Override
	public Function duplicate();

	/**
	 * Duplicates a processor based on a context object
	 * @param c The context
	 * @return A duplicate of the processor
	 */
	public Function duplicate(Context c);
}