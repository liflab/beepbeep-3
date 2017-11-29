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
package ca.uqac.lif.cep.tmf;


import ca.uqac.lif.cep.Processor;

/**
 * Returns one input event and discards the next <i>n</i>-1. The value <i>n</i>
 * is called the <em>decimation interval</em>.
 * However, a mode can be specified in order to output the <i>n</i>-<i>i</i>th input
 * event if it is the last event of the trace and it has not been output already.
 *
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2160")
public class CountDecimate extends Decimate {

    /**
     * Dummy UID
     */
    private static final long serialVersionUID = -1528026169905098741L;

    /**
     * The decimation interval
     */
    private final int m_interval;

    /**
     * Index of last event received
     */
    private int m_current;

    public CountDecimate(int interval, boolean shouldProcessLastInputs) {
        super(shouldProcessLastInputs);
        m_interval = interval;
        m_current = 0;
    }

    public CountDecimate(int interval) {
        this(interval, false);
    }

    public CountDecimate() {
        this(1);
    }

    @Override
    protected boolean shouldOutput() {
        return m_current == 0;
    }

    @Override
    protected void post() {
        m_current = (m_current + 1) % m_interval;
    }

    @Override
    public void reset() {
        super.reset();
        m_current = 0;
    }

    @Override
    public Processor duplicate() {
        return new CountDecimate(m_interval, m_shouldProcessLastInputs);
    }
}
