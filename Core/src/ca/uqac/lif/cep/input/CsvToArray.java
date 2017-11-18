package ca.uqac.lif.cep.input;

import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.util.StringUtils;

public class CsvToArray extends UnaryFunction<String,Object>
{
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
	public Object getValue(String s) throws FunctionException
	{
		String[] parts = s.split(m_separator);
		Object[] typed_parts = new Object[parts.length];
		for (int i = 0; i < parts.length; i++)
		{
			typed_parts[i] = StringUtils.createConstantFromString(parts[i]);
		}
		return typed_parts;
	}
}
