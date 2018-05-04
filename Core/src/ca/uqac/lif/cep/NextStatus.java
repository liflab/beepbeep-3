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
package ca.uqac.lif.cep;

/**
 * The "next" status of a {@link Pullable} object. Indicates whether a new
 * output event is available (i.e. can be "pulled").
 * <ul>
 * <li><code>YES</code> indicates that a new event can be pulled right now,
 * using either {@link #pullSoft()} or {@link #pull()}</li>
 * <li><code>NO</code> indicates that no event is available, and will ever be.
 * Receiving <code>NO</code> generally indicates that the end of the (output)
 * trace has been reached</li>
 * <li><code>MAYBE</code> indicates that no event is available, but that keeping
 * on pulling <em>may </em>produce an event in the future. This value is only
 * returned by {@link #hasNextSoft()}.</li>
 * </ul>
 * 
 * @author Sylvain Hallé
 *
 */
public enum NextStatus
{
  YES, NO, MAYBE;
}
