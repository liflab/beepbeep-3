/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Faucet that applies a function on the last event received
 * @author Sylvain Hallé
 *
 * @param <T> The type of the input
 * @param <U> The type of the output
 */
public class FunctionFaucet<T,U> extends LastFaucet
{
	/**
	 * The function to evaluate
	 */
	protected UnaryFunction<T,U> m_function;
	
	/**
	 * Creates a new function faucet
	 * @param function The function to be applied
	 */
	public FunctionFaucet(UnaryFunction<T,U> function)
	{
		super();
		m_function = function;
	}
	
	@Override
	public U onPull(Object o) throws ProcessorException
	{
		try
		{
			@SuppressWarnings("unchecked")
			U value = m_function.getValue((T) o);
			return value;
		}
		catch (ClassCastException e)
		{
			throw new ProcessorException(e);
		}
		catch (FunctionException e) 
		{
			throw new ProcessorException(e);
		}
	}
}
