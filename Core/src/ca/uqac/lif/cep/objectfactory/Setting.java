package ca.uqac.lif.cep.objectfactory;

/**
 * One of the parameters regulating the instantiation of some object
 */
public class Setting
{
	/**
	 * The name of the parameter
	 */
	protected final String m_name;

	/**
	 * The type (i.e. class) of the parameter
	 */
	protected final Class<?> m_type;

	/**
	 * Determines if the parameter is mandatory. If so,
	 * the processor cannot be instantiated without providing
	 * a value for this parameter.
	 */
	protected final boolean m_mandatory;

	/**
	 * The current value of this setting
	 */
	protected Object m_value;

	/**
	 * The description for this setting
	 */
	protected String m_description = null;

	/**
	 * Instantiates a new setting
	 * @param name The name of the setting
	 * @param type The type of the setting
	 * @param mandatory Whether this setting is mandatory
	 */
	public Setting(String name, Class<?> type, boolean mandatory)
	{
		this(name, type, mandatory, null);
	}

	/**
	 * Instantiates a new setting
	 * @param name The name of the setting
	 * @param type The type of the setting
	 * @param mandatory Whether this setting is mandatory
	 * @param description The description for this setting
	 */
	public Setting(String name, Class<?> type, boolean mandatory, String description)
	{
		super();
		m_name = name;
		m_type = type;
		m_mandatory = mandatory;
		m_value = null;
	}

	/**
	 * Instantiates a new, non mandatory setting
	 * @param name The name of the setting
	 * @param type The type of the setting
	 */
	public Setting(String name, Class<?> type)
	{
		this(name, type, false);
	}

	/**
	 * Gets the name of the setting
	 * @return The name
	 */
	public String getName()
	{
		return m_name;
	}

	/**
	 * Gets the type of the setting
	 * @return The type
	 */
	public Class<?> getType()
	{
		return m_type;
	}

	/**
	 * Determines if this setting is mandatory
	 * @return true if mandatory, false otherwise
	 */
	public boolean isMandatory()
	{
		return m_mandatory;
	}

	/**
	 * Gets the description of this setting
	 * @return The description (may be null)
	 */
	public String getDescription()
	{
		return m_description;
	}

	/**
	 * Sets the description of this setting
	 * @param o The description
	 */
	public void setDescription(String d)
	{
		m_description = d;
	}

	/**
	 * Gets the current value of this setting
	 * @return The value (may be null)
	 */
	public Object getValue()
	{
		return m_value;
	}

	/**
	 * Sets the value of this setting
	 * @param o The value
	 */
	public void setValue(Object o)
	{
		m_value = o;
	}

	@Override
	public Setting clone()
	{
		Setting out = new Setting(m_name, m_type, m_mandatory, m_description);
		out.setValue(getValue());
		return out;
	}
}
