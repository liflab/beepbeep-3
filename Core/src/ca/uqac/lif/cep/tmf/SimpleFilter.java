package ca.uqac.lif.cep.tmf;

import java.util.Queue;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionException;

/**
 * A simple filter that lets input events out by evaluating a
 * condition on them; if the condition evaluates to true, the event
 * is output, otherwise it is discarded.
 * <p>
 * There also exists a more generic type of filter: {@link Filter},
 * whose filtering decision is based on a trace of Booleans instead of
 * a stateless condition.
 *  
 * @see Filter
 * @author Sylvain Hallé
 */
public class SimpleFilter extends SingleProcessor 
{
	/**
	 * The condition to evaluate
	 */
	protected Function m_condition;
	
	/**
	 * An array to store the value of the condition
	 */
	protected Object[] m_conditionValue = new Object[1];

	/**
	 * Creates a new simple filter
	 * @param in_arity The input arity
	 * @param condition A function to evaluate on each input front
	 */
	public SimpleFilter(int in_arity, Function condition)
	{
		super(in_arity, in_arity);
		m_condition = condition;
	}
	
	/**
	 * Creates a new simple filter or arity 1
	 * @param condition A function to evaluate on each input front
	 */
	public SimpleFilter(Function condition)
	{
		this(1, condition);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) throws ProcessorException
	{
		try
		{
			m_condition.evaluate(inputs, m_conditionValue);
		}
		catch (FunctionException e)
		{
			throw new ProcessorException(e);
		}
		if ((Boolean) m_conditionValue[0] == true)
			outputs.add(inputs);
		return true;
	}

	@Override
	public Processor duplicate() 
	{
		return new SimpleFilter(getInputArity(), m_condition.duplicate());
	}
}
