package ca.uqac.lif.cep.ltl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.ConstantFunction;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.functions.SimpleFunction;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.numbers.NumberCast;

public class Predicate extends SimpleFunction
{
	/**
	 * The predicate's name
	 */
	protected String m_name = null;
	
	/**
	 * The predicate's domain for each of its arguments
	 */
	protected Map<String,Set<Object>> m_domains;

	/**
	 * The predicate's domain name for each of its arguments
	 */
	protected String[] m_domainNames;
	
	/**
	 * The definition of this predicate
	 */
	protected Map<PredicateArgument,Troolean.Value> m_definition;
	
	public Predicate(String name, String ...domain_names)
	{
		super();
		m_name = name;
		m_domainNames = domain_names;
		m_domains = new HashMap<String,Set<Object>>();
		for (String d_name : domain_names)
		{
			m_domains.put(d_name, new HashSet<Object>());
		}
		m_definition = new HashMap<PredicateArgument,Troolean.Value>();
	}
	
	public void updateDefinition(Object[] inputs, Troolean.Value value)
	{
		PredicateArgument arg = new PredicateArgument(inputs);
		m_definition.put(arg, value);
		for (int i = 0; i < m_domainNames.length; i++)
		{
			String domain_name = m_domainNames[i];
			Object domain_value = arg.get(i);
			m_domains.get(domain_name).add(domain_value);
		}
	}
	
	public void updateDefinition(PredicateTuple tuple)
	{
		m_definition.put(tuple.m_arguments, tuple.m_value);
		for (int i = 0; i < m_domainNames.length; i++)
		{
			String domain_name = m_domainNames[i];
			Object domain_value = tuple.m_arguments.get(i);
			m_domains.get(domain_name).add(domain_value);
		}
	}
	
	public Set<Object> getValuesForDomain(String domain_name)
	{
		if (!m_domains.containsKey(domain_name))
		{
			return new HashSet<Object>();
		}
		return m_domains.get(domain_name);
	}
	
	public Set<String> getDomainNames()
	{
		return m_domains.keySet();
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_definition);
		return out.toString();
	}

	@Override
	public Object[] compute(Object[] inputs) 
	{
		Object[] value = new Object[1];
		PredicateArgument arg = new PredicateArgument(inputs);
		if (!m_definition.containsKey(arg))
		{
			// Closed world assumption
			value[0] = Troolean.Value.FALSE;
			return value;
		}
		value[0] = m_definition.get(arg);
		return value;
	}

	@Override
	public int getInputArity() 
	{
		return m_domains.size();
	}

	@Override
	public int getOutputArity() 
	{
		return 1;
	}

	@Override
	public void reset() 
	{
		m_definition.clear();
	}

	@Override
	public Predicate clone() 
	{
		Predicate pred = new Predicate(m_name, m_domainNames);
		pred.m_definition.putAll(m_definition);
		pred.m_domains.putAll(m_domains);
		return pred;
	}
	
	@Override
	public Predicate clone(Context context) 
	{
		Predicate pred = new Predicate(m_name, m_domainNames);
		pred.m_definition.putAll(m_definition);
		pred.m_domains.putAll(m_domains);
		pred.setContext(context);
		return pred;
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index)
	{
		if (index >= 0 && index < m_domains.size())
		{
			classes.add(Object.class);
		}
	}

	@Override
	public Class<?> getOutputTypeFor(int index)
	{
		return Troolean.Value.class;
	}
	
	public static class PredicateArgument extends Vector<Object>
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;
		
		public PredicateArgument(Object[] values)
		{
			super(values.length);
			for (Object o : values)
			{
				add(o);
			}
		}
		
		@Override
		public int hashCode()
		{
			return 0;
		}
		
		@Override
		public boolean equals(Object o)
		{
			if (o == null || !(o instanceof Vector))
			{
				return false;
			}
			Vector<?> v = (Vector<?>) o;
			if (v.size() != size())
			{
				return false;
			}
			for (int i = 0; i < size(); i++)
			{
				Object o1 = get(i);
				Object o2 = v.get(i);
				// TODO: detect wildcards better
				if (o1.toString().compareTo("_") != 0 && o2.toString().compareTo("_") != 0 && !(o1.equals(o2)))
				{
					return false;
				}
			}
			return true;
		}
	}
	
	public static class PredicateTuple
	{
		protected PredicateArgument m_arguments;
		
		protected Troolean.Value m_value;
		
		protected String m_name;
		
		public PredicateTuple(String name, Troolean.Value value, Object[] arguments)
		{
			super();
			m_name = name;
			m_arguments = new PredicateArgument(arguments);
			m_value = value;
		}
		
		public String getName()
		{
			return m_name;
		}
		
		public Object getArgument(int index)
		{
			return m_arguments.get(index);
		}
	}
	
	public static class PredicateTupleReader extends FunctionProcessor
	{
		public PredicateTupleReader()
		{
			super(PredicateTupleConversion.instance);
		}
		
		@Override
		public PredicateTupleReader clone()
		{
			return new PredicateTupleReader();
		}
	}
	
	public static class PredicateTupleConversion extends UnaryFunction<Object,PredicateTuple>
	{
		public static final transient PredicateTupleConversion instance = new PredicateTupleConversion();
		
		PredicateTupleConversion()
		{
			super(Object.class, PredicateTuple.class);
		}

		@Override
		public PredicateTuple getValue(Object x)
		{
			if (x instanceof Object[])
			{
				Object[] contents = (Object[]) x;
				String name = (String) contents[0];
				ArrayList<Object> args = new ArrayList<Object>();
				for (int i = 1; i < contents.length; i++)
				{
					// First, filter to remove spurious empty strings
					if (contents[i] != null && !((String) contents[i]).trim().isEmpty())
					{
						args.add(((String) contents[i]).trim());
					}
				}
				Object[] arg_vals = new Object[args.size()];
				for (int i = 0; i < args.size(); i++)
				{
					arg_vals[i] = args.get(i);
				}
				PredicateTuple tuple = new PredicateTuple(name, Troolean.Value.TRUE, arg_vals);
				return tuple;
			}
			else if (x instanceof List)
			{
				List<?> contents = (List<?>) x;
				String name = (String) contents.get(0);
				ArrayList<Object> args = new ArrayList<Object>();
				for (int i = 1; i < contents.size(); i++)
				{
					// First, filter to remove spurious empty strings
					if (contents.get(i) != null && !((String) contents.get(i)).trim().isEmpty())
					{
						args.add(((String) contents.get(i)).trim());
					}
				}
				Object[] arg_vals = new Object[args.size()];
				for (int i = 0; i < args.size(); i++)
				{
					arg_vals[i] = args.get(i);
				}
				PredicateTuple tuple = new PredicateTuple(name, Troolean.Value.TRUE, arg_vals);
				return tuple;				
			}
			else
			{
				// Return dummy tuple
				return new PredicateTuple("", Troolean.Value.FALSE, null);
			}
		}
		
		@Override
		public PredicateTupleConversion clone()
		{
			return this;
		}
	}
	
	public static class Wildcard extends ConstantFunction
	{
		public Wildcard()
		{
			super("_");
		}
		
		@Override
		public Object[] evaluate(Object[] inputs, Context context)
		{
			Object[] out = new Object[1];
			out[0] = this;
			return out;
		}
	}
	
	public static class PredicateGet extends UnaryFunction<PredicateTuple,Object>
	{
		protected int m_position;
		
		public PredicateGet(int position)
		{
			super(PredicateTuple.class, Object.class);
			m_position = position;
		}

		@Override
		public Object getValue(PredicateTuple x) 
		{
			if (m_position == 0)
			{
				return x.m_name;
			}
			if (m_position > x.m_arguments.size())
			{
				return null;
			}
			return x.m_arguments.get(m_position - 1);
		}
		
		@Override
		public PredicateGet clone()
		{
			return new PredicateGet(m_position);
		}
	}
	
	public static class PredicateGetNumber extends UnaryFunction<PredicateTuple,Number>
	{
		protected int m_position;
		
		public PredicateGetNumber(int position)
		{
			super(PredicateTuple.class, Number.class);
			m_position = position;
		}

		@Override
		public Number getValue(PredicateTuple x) 
		{
			if (m_position == 0)
			{
				// This is the predicate's name!
				return 0;
			}
			if (m_position > x.m_arguments.size())
			{
				// > and not >=, as we use position - 1 below
				return -1;
			}
			return NumberCast.getNumber(x.m_arguments.get(m_position - 1));
		}
		
		@Override
		public PredicateGetNumber clone()
		{
			return new PredicateGetNumber(m_position);
		}		
	}
}