package ca.uqac.lif.cep.ltl;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.UnaryFunction;

public class Interpretation
{
	protected Map<String,Set<Object>> m_domains;
	
	protected Map<String,Predicate> m_predicates;
	
	public Interpretation(Map<String,Set<Object>> domains, Map<String,Predicate> predicates)
	{
		super();
		m_domains = domains;
		m_predicates = predicates;
	}
	
	public Set<Object> getDomain(String domain_name)
	{
		if (!m_domains.containsKey(domain_name))
		{
			return new HashSet<Object>();
		}
		return m_domains.get(domain_name);
	}
	
	@SuppressWarnings("rawtypes")
	public static class GetDomain extends UnaryFunction<Interpretation,Set>
	{
		protected String m_domainName;
		
		public GetDomain(String domain_name)
		{
			super(Interpretation.class, Set.class);
			m_domainName = domain_name;
		}

		@Override
		public Set getValue(Interpretation x)
		{
			return x.getDomain(m_domainName);
		}
		
		@Override
		public GetDomain clone()
		{
			return new GetDomain(m_domainName);
		}
	}
	
	public static class PredicateAssertion extends Function
	{
		protected String m_predicateName;
		
		protected Function[] m_arguments;
		
		public PredicateAssertion(String predicate_name, Function ... arguments)
		{
			super();
			m_predicateName = predicate_name;
			m_arguments = arguments;
		}

		@Override
		public Object[] evaluate(Object[] inputs, Context context)
		{
			Interpretation inter = (Interpretation) inputs[0];
			Object[] out = new Object[1];
			if (!inter.m_predicates.containsKey(m_predicateName))
			{
				// Closed world assumption
				out[0] = Troolean.Value.FALSE;
				return out;
			}
			Predicate pred = inter.m_predicates.get(m_predicateName);
			Object[] values = new Object[m_arguments.length];
			for (int i = 0; i < m_arguments.length; i++)
			{
				values[i] = m_arguments[i].evaluate(inputs, context)[0];
			}
			out[0] = pred.evaluate(values, context)[0];
			return out;
		}

		@Override
		public Object[] evaluate(Object[] inputs)
		{
			return evaluate(inputs, null);
		}

		@Override
		public int getInputArity() 
		{
			// Arity is 1, since the assertion recieves an *interpretation*
			// as its input
			return 1;
			//return m_arguments.length;
		}

		@Override
		public int getOutputArity() 
		{
			return 1;
		}

		@Override
		public void reset() 
		{
			for (Function f : m_arguments)
			{
				f.reset();
			}
		}

		@Override
		public Function clone() 
		{
			Function[] arguments = new Function[m_arguments.length];
			for (int i = 0; i < m_arguments.length; i++)
			{
				arguments[i] = m_arguments[i].clone();
			}
			return new PredicateAssertion(m_predicateName, arguments);
		}
		
		@Override
		public Function clone(Context context) 
		{
			Function[] arguments = new Function[m_arguments.length];
			for (int i = 0; i < m_arguments.length; i++)
			{
				arguments[i] = m_arguments[i].clone(context);
			}
			return new PredicateAssertion(m_predicateName, arguments);
		}

		@Override
		public void getInputTypesFor(Set<Class<?>> classes, int index)
		{
			classes.add(Interpretation.class);
			//classes.add(m_arguments[index].getOutputTypeFor(0));
		}

		@Override
		public Class<?> getOutputTypeFor(int index)
		{
			return Troolean.Value.class;
		}	
	}
}