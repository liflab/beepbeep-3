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
package ca.uqac.lif.cep.objectfactory;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

/**
 * Representation of a set of parameters regulating the instantiation of
 * an object.
 * 
 * @author Sylvain Hallé
 *
 */
public class SettingsSet
{
	/**
	 * The method name a class must implement to be instantiated through
	 * a <code>SettingsSet</code> object
	 */
	public static final String s_instanceMethodName = "getNewInstance";
	
	/**
	 * The settings associated to a processor type. Note that this is not a
	 * set, since we might want the settings to be displayed always in the
	 * same order (for example in some GUI).
	 */
	protected final List<Setting> m_settings;
	
	/**
	 * The class this set of settings creates instances of
	 */
	protected final Class<?> m_class;
	
	/**
	 * Creates a new empty set of processor settings
	 */
	public SettingsSet(Class<?> clazz)
	{
		super();
		m_settings = new ArrayList<Setting>();
		m_class = clazz;
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
	public SettingsSet add(Setting s)
	{
		m_settings.add(s);
		return this;
	}
	
	@Override
	public SettingsSet clone()
	{
		SettingsSet out = new SettingsSet(m_class);
		// Clone all settings
		for (Setting s : m_settings)
		{
			out.add(s.clone());
		}
		return out;
	}
	
	/**
	 * Gets a new instance of an object based on the current
	 * settings. This method does the following:
	 * <ol>
	 * <li>If static method <code>getNewInstance()</code> exists in the
	 * target class, invoke it with the current <code>SettingsSet</code>
	 * and return its result</li>
	 * <li>Otherwise, try to create a new instance of the target class
	 * by invoking its empty constructor</li>
	 * <li>Otherwise, fail by throwing an exception</li>
	 * </ol>
	 * @return A new instance of the object
	 * @throws InstantiationException If the instantiation could
	 *   not occur
	 */
	public Object getObject() throws InstantiationException
	{
		Method m = null;
		Object o = null;
		// First, check if method "getNewInstance" exists
		try 
		{
	        m = m_class.getMethod(s_instanceMethodName, SettingsSet.class);
	    } 
		catch (IllegalArgumentException e) 
		{
			// Do nothing
	    } 
		catch (SecurityException e) 
		{
	        // Do nothing
	    } 
		catch (NoSuchMethodException e) 
		{
	        // Do nothing
	    }
		if (m == null)
		{
			// Method does not exist; try to instantiate a vanilla object
			try 
			{
				o = m_class.newInstance();
				return o;
			} 
			catch (java.lang.InstantiationException e) 
			{
				// Do nothing
			} 
			catch (IllegalAccessException e) 
			{
				// Do nothing
			}
			// If we get here, something bad happened
			throw new InstantiationException();
		}
		else
		{
			// Method exists; check if settings are valid
			if (!isComplete())
			{
				// No: fail
				throw new InstantiationException();
			}
			// Invoke method
			try 
			{
				o = m.invoke(null, s_instanceMethodName, this);
				return o;
			} 
			catch (IllegalAccessException e) 
			{
				// Do nothing
			} 
			catch (IllegalArgumentException e) 
			{
				// Do nothing
			} 
			catch (InvocationTargetException e) 
			{
				// Do nothing
			}
			// If we get here, something bad happened
			throw new InstantiationException();
		}
	}
	
	/**
	 * Checks if all mandatory settings of the set are non-null
	 * @return true if all mandatory settings of the set are defined,
	 *   false otherwise
	 */
	public boolean isComplete()
	{
		for (Setting s : m_settings)
		{
			if (s.isMandatory() && s.getValue() == null)
			{
				return false;
			}
		}
		return true;
	}

}
