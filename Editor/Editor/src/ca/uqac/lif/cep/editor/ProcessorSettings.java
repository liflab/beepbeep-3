package ca.uqac.lif.cep.editor;

import java.util.ArrayList;
import java.util.List;

import ca.uqac.lif.json.JsonElement;
import ca.uqac.lif.json.JsonList;
import ca.uqac.lif.json.JsonMap;

public class ProcessorSettings 
{
	/**
	 * The settings associated to a processor type
	 */
	List<Setting> m_settings;
	
	/**
	 * Creates a new empty set of processor settings
	 */
	public ProcessorSettings()
	{
		super();
		m_settings = new ArrayList<Setting>();
	}
	
	/**
	 * Gets a setting with given name
	 * @param name The name
	 * @return The setting, or null if not found
	 */
	public Setting get(String name)
	{
		for (Setting s : m_settings)
		{
			if (name.compareTo(s.getName()) == 0)
			{
				return s;
			}
		}
		return null;
	}
	
	/**
	 * Adds a new setting
	 * @param s The setting
	 * @return This set of settings
	 */
	public ProcessorSettings add(Setting s)
	{
		m_settings.add(s);
		return this;
	}
	
	/**
	 * Produces a JSON structure for this set of settings
	 * @return A well-formed JSON string
	 */
	public JsonElement toJson()
	{
		JsonList list = new JsonList();
		for (Setting s : m_settings)
		{
			list.add(s.toJson());
		}
		return list;
	}

	/**
	 * One of the parameters regulating the operation of some processor
	 */
	public static class Setting
	{
		/**
		 * The name of the parameter
		 */
		protected String m_name;

		/**
		 * The type (i.e. class) of the parameter
		 */
		protected Class<?> m_type;
		
		/**
		 * The current value of this setting
		 */
		protected Object m_value;
		
		/**
		 * Determines if the parameter is mandatory. If so,
		 * the processor cannot be instantiated without providing
		 * a value for this parameter.
		 */
		protected boolean m_mandatory = false;

		/**
		 * Instantiates a new setting
		 * @param name The name of the setting
		 * @param type The type of the setting
		 * @param mandatory Whether this setting is mandatory
		 */
		public Setting(String name, Class<?> type, boolean mandatory)
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
		
		public String getName() 
		{
			return m_name;
		}

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
		
		/**
		 * Produces a JSON structure for this setting
		 * @return A well-formed JSON string
		 */
		public JsonElement toJson()
		{
			JsonMap map = new JsonMap();
			map.put("name", m_name);
			map.put("type", m_type.getName());
			map.put("mandatory", m_mandatory);
			if (m_value != null)
			{
				map.put("value", m_value);
			}
			else
			{
				map.put("value", "null");
			}
			return map;
		}
	}
	
	/**
	 * Processor setting for an Integer
	 */
	public static class IntegerSetting extends Setting
	{
		public IntegerSetting(String name, boolean mandatory)
		{
			super(name, Integer.class, mandatory);
		}
	}
	
	/**
	 * Processor setting for a String
	 */
	public static class StringSetting extends Setting
	{
		public StringSetting(String name, boolean mandatory)
		{
			super(name, String.class, mandatory);
		}
	}

}
