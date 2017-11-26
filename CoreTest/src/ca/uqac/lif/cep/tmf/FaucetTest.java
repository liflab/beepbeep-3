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

import static org.junit.Assert.*;

import org.junit.Test;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;

public class FaucetTest
{
	@Test
	public void test1()
	{
		Object o;
		TankLast faucet = new TankLast();
		Pushable pushable = faucet.getPushableInput();
		Pullable pullable = faucet.getPullableOutput();
		pushable.push("A");
		pushable.push("B");
		o = pullable.pull();
		assertEquals("B", (String) o);
		o = pullable.pull();
		assertEquals("B", (String) o);
		pushable.push("C");
		o = pullable.pull();
		assertEquals("C", (String) o);
	}

}
