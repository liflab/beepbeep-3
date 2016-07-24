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
 * Processors to express complex patterns over sequences of events
 * with a first-order extension of Linear Temporal Logic called
 * LTL-FO+.
 * <p>
 * Temporal operators and quantifiers have processors in two versions:
 * Boolean and <em>Troolean</em>.
 * <p>
 * Boolean processors are called {@link Globally}, {@link Eventually}
 * {@link Until}, {@link Next}, {@link ForAll} and {@link Exists}.
 * If a<sub>0</sub> a<sub>1</sub>
 * a<sub>2</sub> &hellip; is an input trace, the processor Globally
 * produces an output trace b<sub>0</sub> b<sub>1</sub>
 * b<sub>2</sub> &hellip; such that b<sub>i</sub> = false if and only
 * there exists j &geq; i such that b<sub>j</sub> = false. In other
 * words, the i-th output event is the Boolean verdict of evaluating
 * <b>G</b> &phi; on the input trace, starting at the i-th event.
 * <p>
 * Troolean processors are called {@link Always}, {@link Sometime},
 * {@link UpTo}, {@link After}, {@link Every} and {@link Some}.
 * If a<sub>0</sub> a<sub>1</sub>
 * a<sub>2</sub> &hellip; is an input trace, the processor Always
 * produces an output trace b<sub>0</sub> b<sub>1</sub>
 * b<sub>2</sub> &hellip; such that b<sub>i</sub> = false if there exists
 * j &leq; i such that b<sub>j</sub> = false, and "?" (the
 * "inconclusive" value of LTL<sub>3</sub>) otherwise.  In other
 * words, the i-th output event is the Boolean verdict of evaluating
 * <b>G</b> &phi; on the input trace, after reading i events.
 * 
 * 
 * @author Sylvain Hallé
 */
package ca.uqac.lif.cep.ltl;