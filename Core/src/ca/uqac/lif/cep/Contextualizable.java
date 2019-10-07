package ca.uqac.lif.cep;

public interface Contextualizable
{
	public Object getContext(String key);
	
	public void setContext(String key, Object value);

}
