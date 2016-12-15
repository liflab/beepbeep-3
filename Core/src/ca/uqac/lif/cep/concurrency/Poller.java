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
package ca.uqac.lif.cep.concurrency;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.NextStatus;

interface Poller extends Runnable
{
	public static enum Call {NONE, HAS_NEXT, HAS_NEXT_SOFT, PULL, PULL_SOFT};

	public boolean isDone();

	public void call(Call c);

	public NextStatus getNextSoftStatus();

	public boolean getNextHardStatus();

	public Object getNextSoft();

	public Object getNextHard();

	public void stop();

	public Pullable getPullable();

	public void dispose();

}
