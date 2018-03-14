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

/**
 * Elementary classes defining all the basic concepts of event stream
 * processing. Here are some of the important objects defined in this
 * package.
 * 
 * - A {@link ca.uqac.lif.cep.Processor Processor} is an object that takes zero or
 *   more event *streams*, and produces zero or more event
 *   *streams* as its output.
 * - {@link ca.uqac.lif.cep.Pullable Pullable} and
 *   {@link ca.uqac.lif.cep.Pushable Pushable} are two interfaces for
 *   receiving and giving events from/to a processor, respectively.
 * - {@link ca.uqac.lif.cep.Connector Connector} provides static
 *   methods for easily linking one processor's output to another's input
 * 
 * @author Sylvain Hallé
 */
package ca.uqac.lif.cep;