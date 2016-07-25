package ca.uqac.lif.cep.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Queue;
import java.util.Scanner;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * Special case of stream reader reading lines from a text file.
 * @author Sylvain Hallé
 *
 */
public class LineReader extends SingleProcessor 
{
	/**
	 * The scanner to read from
	 */
	protected Scanner m_scanner;
	
	/**
	 * The file to read from
	 */
	protected File m_file;
	
	/**
	 * Whether to add a carriage return at the end of each line
	 */
	protected boolean m_addCrlf = true;
	
	public LineReader(File f)
	{
		super(0, 1);
		m_file = f;
		try 
		{
			m_scanner = new Scanner(f);
		} 
		catch (FileNotFoundException e) 
		{
			e.printStackTrace();
		}
	}
	
	/*@Override
	public Pullable getPullableOutput(int index)
	{
		return new SentinelPullable();
	}*/

	@Override
	protected Queue<Object[]> compute(Object[] inputs) 
	{
		if (m_scanner.hasNextLine())
		{
			String line = m_scanner.nextLine();
			if (m_addCrlf)
			{
				line += "\n";
			}
			return wrapObject(line);
		}
		return null;
	}

	@Override
	public Processor clone() 
	{
		return new LineReader(m_file);
	}
}
