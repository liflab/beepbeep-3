package ca.uqac.lif.cep;

import org.junit.Test;

import ca.uqac.lif.cep.Processor.NthEvent;
import ca.uqac.lif.cep.tmf.CountDecimate;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.graph.ConcreteTraceabilityNode;
import ca.uqac.lif.petitpoucet.graph.ConcreteTracer;
import ca.uqac.lif.petitpoucet.graph.render.TraceabilityNodeDotRenderer;


public class ProvenanceDemo {

	public static void main(String[] args) 
	{
		QueueSource qs = new QueueSource().setEvents(2, 7, 1, 8, 2, 8, 1, 8, 2).loop(true);
		CountDecimate cd = new CountDecimate(3);
		Connector.connect(qs, cd);
		Passthrough pt = new Passthrough();
		Connector.connect(cd, pt);
		ConcreteTracer tracer = new ConcreteTracer();
		//ComposedDesignator d = new ComposedDesignator(new NthEvent(4), new NthOutput(0));
		//ConcreteTraceabilityNode root = tracer.getTree(TraceabilityQuery.ProvenanceQuery.instance, d, pt.getQueryable());
		ComposedDesignator d = new ComposedDesignator(new NthEvent(3), new NthOutput(0));
		ConcreteTraceabilityNode root = tracer.getTree(TraceabilityQuery.TaintQuery.instance, d, qs.getQueryable());
		TraceabilityNodeDotRenderer renderer = new TraceabilityNodeDotRenderer();
		renderer.setFlatten(false);
		String out = renderer.render(root);
		System.out.println(out);
	}
	
	@Test
	public void dummyTest()
	{
		
	}

}
