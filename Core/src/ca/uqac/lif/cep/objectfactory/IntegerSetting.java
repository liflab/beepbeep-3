package ca.uqac.lif.cep.objectfactory;

/**
 * Object setting for an Integer
 */
public class IntegerSetting extends Setting
{
	public IntegerSetting(String name, boolean mandatory, String description)
	{
		super(name, Integer.class, mandatory, description);
	}
	
	public IntegerSetting(String name, boolean mandatory)
	{
		super(name, Integer.class, mandatory);
	}
	
	/**
	 * Gets the setting's value, cast as an integer
	 * @return The value
	 */
	public int getIntValue()
	{
		return (Integer) m_value;
	}
}
