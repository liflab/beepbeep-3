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
package ca.uqac.lif.cep;

/**
 * Interface indicating that an object can be duplicated. Note that
 * while duplication looks very similar to cloning, it is actually
 * different. A duplicated object may not have the exact same state as
 * the original. This is particularly true of {@link Processor} objects,
 * which <em>always</em> have a different numerical ID. Moreover,
 * duplication may be dependent on a {@link Context} object, which cannot
 * be the case with Java's meaning of cloning. Hence the need for a
 * different interface.
 * 
 * @author Sylvain Hallé
 *
 */
public interface Duplicable
{
	/**
	 * Duplicates an object
	 * @return Another object
	 */
	public Object duplicate();
	
}
