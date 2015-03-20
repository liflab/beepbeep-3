package ca.uqac.lif.cep;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Vector;

public class WindowProcessor extends Processor
{
	/**
	 * The window's width
	 */
	protected int m_width;
	
	/**
	 * The internal processor
	 */
	protected Processor m_processor;
	
	/**
	 * The event window
	 */
	protected List<Queue<Object>> m_window;
	
	public WindowProcessor(Processor in_processor, int width)
	{
		super(in_processor.getInputArity(), in_processor.getOutputArity());
		m_width = width;
		//m_window = new LinkedList<Object>();
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		// Is the 
		// TODO Auto-generated method stub
		return null;
	}

}
