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

/**
 * After returning an input event, discards all others for the next
 * <i>n</i> seconds. This processor therefore acts as a rate limiter.
 * <p>
 * Note that this processor uses <code>System.currentTimeMillis()</code>
 * as its clock.
 * Moreover, a mode can be specified in order to output the last input
 * event of the trace if it has not been output already.
 *
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2160")
public class TimeDecimate extends Decimate {

    /**
     *
     */
    private static final long serialVersionUID = -7825576479352779012L;

    /**
     * Interval of time
     */
    protected final long m_interval;

    /**
     * The system time when the last event was output
     */
    protected long m_timeLastSent;

    /**
     * Instantiates a time decimator
     * @param interval The interval (in milliseconds) during which
     *   events should be discarded after an output event is produced
     * @param shouldProcessLastInputs Default to false. Indicates if
     *   the last input event of the trace should be output in case it
     *   does not match the decimation interval
     */
    public TimeDecimate(long interval, boolean shouldProcessLastInputs) {
        super(shouldProcessLastInputs);
        m_interval = interval;
        m_timeLastSent = -1;
    }

    /**
     * Instantiates a time decimator
     * @param interval The interval (in milliseconds) during which
     *   events should be discarded after an output event is produced
     */
    public TimeDecimate(long interval) {
        this(interval, false);
    }

    /**
     * Gets the time decimation interval
     * @return The interval (in milliseconds) during which
     *   events should be discarded after an output event is produced
     */
    public long getInterval()
    {
        return m_interval;
    }

    @Override
    protected boolean shouldOutput() {
        return m_timeLastSent < 0 || (System.currentTimeMillis() - m_timeLastSent) >= m_interval;
    }

    @Override
    protected void postOutput() {
        m_timeLastSent = System.currentTimeMillis();
    }

    @Override
    public void reset() {
        super.reset();
        m_timeLastSent = -1;
    }

    @Override
    public TimeDecimate duplicate() {
        return new TimeDecimate(m_interval, m_shouldProcessLastInputs);
    }
}
