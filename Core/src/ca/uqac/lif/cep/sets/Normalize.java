package ca.uqac.lif.cep.sets;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.NothingToReturnException;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Normalizes a collection of numbers
 * @author Sylvain Hallé
 */
public class Normalize extends UnaryFunction<Object,Object> 
{
	public static final transient Normalize instance = new Normalize();
	
	protected Normalize()
	{
		super(Object.class, Object.class);
	}

	@SuppressWarnings("unchecked")
	@Override
	public Object getValue(Object x) throws FunctionException
	{
		if (x instanceof Collection)
		{
			Collection<Number> l1 = (Collection<Number>) x;
			List<Number> l2 = new ArrayList<Number>(l1.size());
			float sum = 0;
			for (Number n : l1)
			{
				sum += n.floatValue();
			}
			if (sum == 0)
			{
				throw new NothingToReturnException(this);
			}
			for (Number n : l1)
			{
				l2.add(n.floatValue() / sum);
			}
			return l2;
		}
		return null;
	}

}
