package ca.uqac.lif.cep.objectfactory;

/**
 * Object setting for a String
 */
public class StringSetting extends Setting
{
	public StringSetting(String name, boolean mandatory)
	{
		super(name, String.class, mandatory);
	}
}
