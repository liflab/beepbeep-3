/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

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
package ca.uqac.lif.cep.jdbc;

import java.sql.ResultSet;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.io.StreamGrammar;
import ca.uqac.lif.cep.tuples.TupleGrammar;

public class BeepBeepStatement extends EmptyStatement
{
	protected final Interpreter m_interpreter;
	
	BeepBeepStatement(Interpreter interpreter)
	{
		super();
		m_interpreter = interpreter;
		// Load a few extensions
		m_interpreter.extendGrammar(StreamGrammar.class);
		m_interpreter.extendGrammar(TupleGrammar.class);
	}
	
	@Override
	public ResultSet executeQuery(String query)
	{
		Pullable p = m_interpreter.executeQuery(query);
		return new BeepBeepResultSet(p);
	}
}
