/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2022 Sylvain Hallé

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
 * Interface implemented by processors that can publicly expose a token
 * equivalent to their internal state. This token can be an arbitrary
 * object, except <tt>null</tt>. However, it must follow this condition:
 * if two processor instances &pi;<sub>1</sub> and &pi;<sub>2</sub> (of
 * the same class) respectively return two state tokens <i>s</i><sub>1</sub>
 * and <i>s</i><sub>2</sub> such that 
 * <i>s</i><sub>1</sub><tt>.equals(</tt><i>s</i><sub>2</sub><tt>) ==
 * true</tt>, then for any sequence of inputs, &pi;<sub>1</sub>
 * and &pi;<sub>2</sub> must generate the same output.
 * 
 * @author Sylvain Hallé
 * @since 0.11
 */
public interface PubliclyStateful
{
	/**
	 * Gets the token corresponding to the processor's internal state.
	 * @return The token
	 */
	/*@ non_null @*/ public Object getState();
}
