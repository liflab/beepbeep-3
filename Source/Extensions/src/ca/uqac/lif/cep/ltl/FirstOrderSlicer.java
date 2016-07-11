package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.CumulativeProcessor;
import ca.uqac.lif.cep.Function;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.epl.Slicer;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public abstract class FirstOrderSlicer extends GroupProcessor
{
	FirstOrderSlicer(Function slicing_function, Processor p) throws ConnectorException
	{
		super(1, 1);
		Slicer slicer = new Slicer(slicing_function, p);
		CumulativeProcessor merge = new CumulativeProcessor(getMergeFunction());
		Connector.connect(slicer, merge);
		addProcessors(slicer, merge);
	}
	
	protected abstract CumulativeFunction<Value> getMergeFunction(); 
}
