package ca.uqac.lif.cep;

public interface Contextualizable
{
	/**
	 * Adds a complete context to this object
	 * @param context The context to add
	 */
	public void setContext(Context context);

	/**
	 * Adds an object to the object's context
	 * @param key The key associated to that object
	 * @param value The object
	 */
	public void setContext(String key, Object value);

	/**
	 * Gets the context associated to this object
	 * @return The context
	 */
	public Context getContext();
}
