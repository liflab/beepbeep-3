package ca.uqac.lif.cep.sets;

import java.util.ArrayList;
import java.util.List;

import ca.uqac.lif.cep.functions.UnaryFunction;

@SuppressWarnings("rawtypes")
public class CsvToList extends UnaryFunction<String, List>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 8652652785650191093L;
	/**
	 * Instance of the function
	 */
	public static final transient CsvToList instance = new CsvToList();

	CsvToList()
	{
		super(String.class, List.class);
	}

	@Override
	public List getValue(String x)
	{
		String[] array = x.split(",");
		List<String> out = new ArrayList<String>(array.length);
		for (String s : array)
		{
			out.add(s.trim());
		}
		return out;
	}

}
