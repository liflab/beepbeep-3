package ca.uqac.lif.cep.input;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;
import java.util.regex.Pattern;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.UniformProcessor;

public class TokenScanner extends UniformProcessor
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 2574308236776766938L;

	/**
	 * The scanner to read from
	 */
	protected Scanner m_scanner;

	/**
	 * The file to read from
	 */
	protected File m_file;

	/**
	 * The pattern to read from
	 */
	protected Pattern m_pattern;

	/**
	 * Whether to add a carriage return at the end of each line
	 */
	protected boolean m_addCrlf = true;

	public TokenScanner(File f, String pattern)
	{
		super(0, 1);
		m_file = f;
		try
		{
			m_scanner = new Scanner(f);
		}
		catch (FileNotFoundException e)
		{
			throw new ProcessorException(e);
		}
		m_pattern = Pattern.compile(pattern);
	}

	@Override
	@SuppressWarnings("squid:S1168")
	protected boolean compute(Object[] inputs, Object[] outputs)
	{
		if (m_scanner.hasNext(m_pattern))
		{
			String line = m_scanner.next(m_pattern);
			if (m_addCrlf)
			{
				line += "\n";
			}
			outputs[0] = line;
			return true;
		}
		return false;
	}

	@Override
	public TokenScanner duplicate()
	{
		return new TokenScanner(m_file, m_pattern.toString());
	}
}
