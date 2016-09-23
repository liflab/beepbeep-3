/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

import java.util.ArrayList;
import java.util.List;

/**
 * Representation of a set of parameters regulating the instantiation and the
 * operation of a processor.
 * 
 * @author Sylvain Hallé
 *
 */
public class ProcessorSettings 
{
	/**
	 * The settings associated to a processor type. Note that this is not a
	 * set, since we might want the settings to be displayed always in the
	 * same order (for example in some GUI).
	 */
	protected final List<Setting> m_settings;
	
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
