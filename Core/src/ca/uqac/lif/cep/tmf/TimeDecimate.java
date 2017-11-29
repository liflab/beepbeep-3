package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.Processor;

/**
 * After returning an input event, discards all others for the next
 * <i>n</i> seconds. This processor therefore acts as a rate limiter.
 * <p>
 * Note that this processor uses <code>System.nanoTime()</code> as its
 * clock.
 * However, a mode can be specified in order to output the last input
 * event of the trace if it has not been output already.
 *
 * @author Sylvain Hallé
 */
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


    public TimeDecimate(long interval, boolean shouldProcessLastInputs) {
        super(shouldProcessLastInputs);
        m_interval = interval;
        m_timeLastSent = -1;
    }

    public TimeDecimate(long interval) {
        this(interval, false);
    }

    @Override
    protected boolean shouldOutput() {
        return m_timeLastSent < 0 || (System.nanoTime() - m_timeLastSent) >= m_interval;
    }

    @Override
    protected void post() {
        m_timeLastSent = System.nanoTime();
    }

    @Override
    public void reset() {
        super.reset();
        m_timeLastSent = -1;
    }

    @Override
    public Processor duplicate() {
        return new TimeDecimate(m_interval, m_shouldProcessLastInputs);
    }
}
