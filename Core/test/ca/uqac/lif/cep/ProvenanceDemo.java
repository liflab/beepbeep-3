package ca.uqac.lif.cep;

import org.junit.Test;

import ca.uqac.lif.cep.Processor.NthEvent;
import ca.uqac.lif.cep.TestUtilities.TestableSingleProcessor;
import ca.uqac.lif.cep.tmf.CountDecimate;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Window;
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
		CountDecimate cd = new CountDecimate(4);
		Connector.connect(qs, cd);
		Window win = new Window(new TestableSingleProcessor(1, 1), 2);
		Connector.connect(cd, win);
		Pullable p = win.getPullableOutput();
		p.pull();
		p.pull();
		p.pull();
		p.pull();
		ConcreteTracer tracer = new ConcreteTracer();
		ComposedDesignator d = new ComposedDesignator(new NthEvent(2), NthOutput.get(0));
		ConcreteTraceabilityNode root = tracer.getTree(TraceabilityQuery.ProvenanceQuery.instance, d, win.getQueryable());
		//ComposedDesignator d = new ComposedDesignator(new NthEvent(3), NthOutput.get(0));
		//ConcreteTraceabilityNode root = tracer.getTree(TraceabilityQuery.TaintQuery.instance, d, qs.getQueryable());
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
