package ca.uqac.lif.cep.input;

import ca.uqac.lif.cep.functions.UnaryFunction;

public class CsvToArray extends UnaryFunction<String,Object>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -1496355704602761974L;

	/**
	 * An instance of this function with default values 
	 */
	public static final transient CsvToArray instance = new CsvToArray(":");
	
	/**
	 * The symbol used to separate data fields
	 */
	protected String m_separator = ":";
	
	public CsvToArray(String separator)
	{
		super(String.class, Object.class);
		m_separator = separator;
	}

	@Override
	public Object getValue(String s) 
	{
		String[] parts = s.split(m_separator);
		Object[] typed_parts = new Object[parts.length];
		for (int i = 0; i < parts.length; i++)
		{
			typed_parts[i] = createConstantFromString(parts[i]);
		}
		return typed_parts;
	}
	
	/**
	 * Attempts to create a constant based on the contents of a string.
	 * That is, if the string contains only digits, it will create an
	 * number instead of a string.
	 * @param s The string to read from
	 * @return The constant
	 */
	public static Object createConstantFromString(String s)
	{
		try
		{
			return Integer.parseInt(s); 
		}
		catch (NumberFormatException nfe1)
		{
			try
			{
				return Float.parseFloat(s);
			}
			catch (NumberFormatException nfe2)
			{
				// Do nothing
			}
		}
		// This is a string
		return s;
	}
}
