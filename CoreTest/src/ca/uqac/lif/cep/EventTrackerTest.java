package ca.uqac.lif.cep;

import static org.junit.Assert.*;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.CumulativeProcessor;
import ca.uqac.lif.cep.functions.CumulativeProcessor.StartValue;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.functions.Negation;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.petitpoucet.DirectValue;
import ca.uqac.lif.petitpoucet.ProvenanceNode;

public class EventTrackerTest 
{
	@Test
	public void testFunctionUnary() throws ConnectorException
	{
		EventTracker tracker = new EventTracker();
		FunctionProcessor add = new FunctionProcessor(Negation.instance);
		QueueSource source = new QueueSource(1);
		source.addEvent(true);
		Connector.connect(source, add);
		tracker.setTo(source, add);
		int add_id = add.getId();
		Pullable p = add.getPullableOutput();
		p.pull();
		ProvenanceNode node = tracker.getProvenanceNode(add_id, 0, 0);
		assertEquals(1, node.getParents().size());
		p.pull();
		node = tracker.getProvenanceNode(add_id, 0, 1);
		assertEquals(1, node.getParents().size());
	}
	
	@Test
	public void testFunctionBinary() throws ConnectorException
	{
		EventTracker tracker = new EventTracker();
		FunctionProcessor add = new FunctionProcessor(Addition.instance);
		QueueSource source1 = new QueueSource(1);
		source1.addEvent(1).addEvent(2);
		QueueSource source2 = new QueueSource(1);
		source2.addEvent(3).addEvent(4).addEvent(5);;
		Connector.connect(source1, 0, add, 0);
		Connector.connect(source2, 0, add, 1);
		tracker.setTo(source1, source2, add);
		int add_id = add.getId();
		Pullable p = add.getPullableOutput();
		p.pull();
		ProvenanceNode node = tracker.getProvenanceNode(add_id, 0, 0);
		assertEquals(2, node.getParents().size());
		p.pull();
		node = tracker.getProvenanceNode(add_id, 0, 1);
		assertEquals(2, node.getParents().size());
	}
	
	@Test
	public void testFunctionCumulative() throws ConnectorException
	{
		EventTracker tracker = new EventTracker();
		CumulativeProcessor add = new CumulativeProcessor(new CumulativeFunction<Number>(Addition.instance));
		QueueSource source = new QueueSource(1);
		source.addEvent(1);
		Connector.connect(source, add);
		tracker.setTo(source, add);
		int add_id = add.getId();
		Pullable p = add.getPullableOutput();
		p.pull();
		ProvenanceNode node = tracker.getProvenanceNode(add_id, 0, 0);
		assertEquals(2, node.getParents().size());
		InputValue ei1 = (InputValue) node.getParents().get(0).getNodeFunction();
		assertEquals(0, ei1.m_streamIndex);
		assertEquals(0, ei1.m_streamPosition);
		StartValue sv1 = (StartValue) node.getParents().get(1).getNodeFunction();
		assertEquals(0, sv1.m_streamIndex); 
		p.pull();
		node = tracker.getProvenanceNode(add_id, 0, 1);
		assertEquals(2, node.getParents().size());
		ei1 = (InputValue) node.getParents().get(0).getNodeFunction();
		assertEquals(0, ei1.m_streamIndex);
		assertEquals(1, ei1.m_streamPosition);
		OutputValue ov2 = (OutputValue) node.getParents().get(1).getNodeFunction();
		assertEquals(0, ov2.m_streamIndex);
		assertEquals(0, ov2.m_streamPosition);
		assertEquals(add_id, ov2.m_processorId);
		p.pull();
		node = tracker.getProvenanceNode(add_id, 0, 2);
		assertEquals(2, node.getParents().size());
		ei1 = (InputValue) node.getParents().get(0).getNodeFunction();
		assertEquals(0, ei1.m_streamIndex);
		assertEquals(2, ei1.m_streamPosition);
		ov2 = (OutputValue) node.getParents().get(1).getNodeFunction();
		assertEquals(0, ov2.m_streamIndex);
		assertEquals(1, ov2.m_streamPosition);
		assertEquals(add_id, ov2.m_processorId);
	}
}
