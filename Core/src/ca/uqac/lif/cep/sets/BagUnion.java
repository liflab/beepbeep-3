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
package ca.uqac.lif.cep.sets;

import ca.uqac.lif.cep.functions.CumulativeFunction;

/**
 * Accumulates the received events cumulatively into a multiset.
 * <p>
 * <b>Example:</b> suppose the input events are integers. From the input
 * trace
 * <pre>
 * 0, 1, 2, 1, 3, ...
 * </pre>
 * the processor will produce the output trace
 * <pre>
 * {0}, {0, 1}, {0, 1, 2}, {0, 1, 1, 2}, {0, 1, 1, 2, 3}, ...
 * </pre>
 * @author Sylvain Hallé
 */
public class BagUnion extends CumulativeFunction<Multiset>
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -7459604471060231209L;

	/**
	 * Note that BagUnion <strong>cannot</strong> have a single static
	 * instance, as a cumulative function has a memory
	 */
	public BagUnion()
	{
		super(MultisetUnion.instance);
	}

}
