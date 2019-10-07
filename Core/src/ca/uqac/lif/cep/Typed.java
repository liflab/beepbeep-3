package ca.uqac.lif.cep;

public interface Typed 
{
	/*@ nullable @*/ public Class<?> getType();
	
	public static class Variant
	{
		// Empty class
	}
}
