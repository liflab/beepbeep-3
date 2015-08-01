/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.eml.tuples;

import java.util.Map;


public class Addition extends BinaryExpression
{
	@Override
	public EmlConstant evaluate(Map<String,Tuple> inputs)
	{
		Tuple t_left = m_left.evaluate(inputs);
		Tuple t_right = m_right.evaluate(inputs);
		if (t_left instanceof EmlNumber && t_right instanceof EmlNumber)
		{
			EmlNumber n_left = (EmlNumber) t_left;
			EmlNumber n_right = (EmlNumber) t_right;
			return new EmlNumber(n_left.numberValue().floatValue() + n_right.numberValue().floatValue());
		}
		return null;
	}
}
