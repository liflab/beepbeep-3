package ca.uqac.lif.cep;

import java.util.Iterator;

import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;

public interface Pullable extends CircuitConnection, Indexed, Iterator<Object>, Typed
{
	public enum NextStatus {YES, NO, MAYBE}
	
	public Object pull();
	
	@Override
	public boolean hasNext();
	
	@Override
	public Object next();
	
	/**
	 * Gets the processor associated to this Pullable
	 * @return The processor; may <em>not</em> be null
	 */
	@Override
	/*@ non_null @*/ public Processor getObject();
	
	/**
	 * @deprecated
	 * @return The next state
	 */
	@Deprecated
	public NextStatus hasNextSoft();
	
	/**
	 * @deprecated
	 * @return
	 */
	@Deprecated
	public Object pullSoft();
}
