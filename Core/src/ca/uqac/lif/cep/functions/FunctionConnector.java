package ca.uqac.lif.cep.functions;

import ca.uqac.lif.petitpoucet.circuit.CircuitConnection;
import ca.uqac.lif.petitpoucet.circuit.CircuitElement;

class FunctionConnector 
{
	private FunctionConnector()
	{
		super();
	}
	
	public static void connect(Function f, int i, Function g, int j)
	{
		f.setToOutput(i, new FunctionConnection(g, i));
		g.setToInput(j, new FunctionConnection(f, i));
	}
	
	static class FunctionConnection implements CircuitConnection
	{
		protected int m_index;
		
		protected Function m_function;
		
		public FunctionConnection(Function f, int index)
		{
			super();
			m_index = index;
			m_function = f;
		}
		
		@Override
		public int getIndex()
		{
			return m_index;
		}

		@Override
		public CircuitElement getObject() 
		{
			return m_function;
		}
		
	}
}
