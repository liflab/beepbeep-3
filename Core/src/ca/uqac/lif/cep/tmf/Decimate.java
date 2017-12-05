package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.SingleProcessor;

import java.util.Queue;


/**
 * By default, a {@link Decimate} acts like a {@link Passthrough} for
 * which only certain inputs are allowed to be output. We call
 * <i>decimation interval</i> the interval between two outputs. The strategy to
 * allow events to be output should be defined in {@link #shouldOutput()},
 * and an update of the state should be done in {@link #postCompute()}.
 * However, it is possible to completely customize a {@link Decimate} by
 * overriding {@link #processInputs(Object[])} and {@link #postOutput()}.
 *
 * Practical examples of {@link Decimate} processors are the {@link CountDecimate},
 * which outputs the first event of a window of size <i>n</i> and discards
 * all the other, and the {@link TimeDecimate} which outputs an input event
 * and discards all others for the next <i>n</i> nanoseconds.
 *
 * In case the processor is notified of the end of the trace (EOT, i.e. there
 * is no more event to compute), by default the processor does not output anything,
 * meaning that the last input event will never be processed nor output (except
 * if it matched the decimation interval). Nevertheless, it is possible to specify
 * that you do want to process and output the last input even if it does not
 * match the decimation interval by passing true to {@link #Decimate(boolean)}.
 *
 * @author Quentin Betti
 */
public abstract class Decimate extends SingleProcessor {


    /**
     * Indicates whether or not the last input event of
     * the trace should be processed and output even if
     * it should not due to the decimation interval
     */
    protected final boolean m_shouldProcessLastInputs;

    /**
     * The last inputs processed by {@link #processInputs(Object[])} stored (in case of EOT processing mode)
     */
    protected Object[] m_lastProcessedInputs;


    /**
     * @param shouldProcessLastInputs set it to true if you want the last input
     *                                to be processed even if it does not correspond
     *                                to the decimation interval, by default is false
     */
    public Decimate(boolean shouldProcessLastInputs) {
        super(1, 1);
        m_shouldProcessLastInputs = shouldProcessLastInputs;
        m_lastProcessedInputs = null;
    }

    public Decimate() {
        this(false);
    }


    @Override
    protected boolean compute(Object[] inputs, Queue<Object[]> outputs) throws ProcessorException {
        m_inputCount++;
        if(shouldOutput())
        {
            Object[] outs = processInputs(inputs);
            outputs.add(outs);
            postOutput();
            m_lastProcessedInputs = null;
            updateEventTracker();

        }
        else if(m_shouldProcessLastInputs)
        {
            m_lastProcessedInputs = processInputs(inputs);
        }

        postCompute();
        return true;
    }


    @Override
    protected boolean onEndOfTrace(Queue<Object[]> outputs) throws ProcessorException {
        if(!m_shouldProcessLastInputs || m_lastProcessedInputs == null)
            return false;

        outputs.add(m_lastProcessedInputs);
        m_lastProcessedInputs = null;
        updateEventTracker();

        return true;

    }

    private final void updateEventTracker() {
        m_outputCount++;
        if (m_eventTracker != null)
        {
            for (int i = 0; i < getInputArity(); i++)
            {
                associateToInput(i, m_inputCount - 1, i, m_outputCount - 1);
            }
        }
    }

    /**
     * Indicates if the inputs should be processed and output
     *
     * @return true if the the inputs should be processed and output, false otherwise
     */
    protected abstract boolean shouldOutput();

    /**
     * Called after each compute. It should mainly be used
     * to update the state of the decimation (e.g. update a counter).
     * By default does nothing.
     */
    protected void postCompute() {}

    /**
     * Method to override if you do not want to output inputs
     * only but also need to calculate a specific output.
     *
     * @param inputs the current input events
     * @return the result that will be added to the outputs, by default returns the inputs as they are
     */
    protected Object[] processInputs(Object[] inputs) {
        return inputs;
    }

    /**
     * Called after every output. Should be used to update a state after an output
     * front has been produced (e.g. storing the time of the last output event production).
     * By default does nothing.
     */
    protected void postOutput() {}

}
