package ca.uqac.lif.cep.epl;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.SingleProcessor;

/**
 * Takes a set of elements as input, and returns as many output
 * events as there are elements in that set.
 * 
 * @author Sylvain Hallé
 */
public class Dropper extends SingleProcessor 
{
	public Dropper()
	{
		super(1, 1);
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object o = inputs[0];
		if (o instanceof Set)
		{
			Set<?> s_o = (Set<?>) o;
			Queue<Object[]> out_queue = new LinkedList<Object[]>();
			for (Object obj : s_o)
			{
				Object[] obj_array = new Object[1];
				obj_array[0] = obj;
				out_queue.add(obj_array);
			}
			return out_queue;
		}
		else
		{
			return wrapObject(o);
		}
	}

	@Override
	public Dropper clone() 
	{
		return new Dropper();
	}
	
	
}
