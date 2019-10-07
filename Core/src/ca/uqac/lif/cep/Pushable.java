package ca.uqac.lif.cep;

import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;

public interface Pushable extends CircuitConnection, Indexed, Typed
{
	public void push(Object o);
	
	public void end();
	
	/**
	 * Gets the processor associated to this Pushable
	 * @return The processor; may <em>not</em> be null
	 */
	@Override
	/*@ non_null @*/ public Processor getObject();
}
