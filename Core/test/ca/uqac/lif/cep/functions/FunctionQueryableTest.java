package ca.uqac.lif.cep.functions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class FunctionQueryableTest
{
	public static Map<String,Object> getPrintedMap(String reference, int in_arity, int out_arity, Object contents)
	{
		Map<String,Object> printed = new HashMap<String,Object>();
		printed.put(FunctionQueryable.s_referenceKey, reference);
		List<Integer> arities = new ArrayList<Integer>(2);
		arities.add(in_arity);
		arities.add(out_arity);
		printed.put(FunctionQueryable.s_arityKey, arities);
		if (contents != null)
		{
			printed.put(FunctionQueryable.s_contentsKey, contents);
		}
		return printed;
	}
}
