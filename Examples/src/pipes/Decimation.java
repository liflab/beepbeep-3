package pipes;

import static ca.uqac.lif.cep.Connector.connect;
import static ca.uqac.lif.cep.Connector.LEFT;
import static ca.uqac.lif.cep.Connector.INPUT;
import static ca.uqac.lif.cep.Connector.OUTPUT;
import static ca.uqac.lif.cep.Connector.RIGHT;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.tmf.CountDecimate;
import ca.uqac.lif.cep.tmf.Fork;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Trim;

/**
 * Computes the sum of every pair of successive events. Here we are
 * interested in computing the sum of events 0+1, 2+3, 4+5, etc.
 * To do so, we compute first the sum of every two successive events,
 * and then keep every other event of the resulting trace.
 * We should obtain 11, 11, 11, 8, 9, 6, 13, 20, ...
 * 
 * @author Sylvain Hallé
 */
public class Decimation 
{
	public static void main(String[] args) throws ConnectorException
	{
		// Create a trace of dummy values
		QueueSource source_values = new QueueSource();
		source_values.setEvents(new Integer[]{6, 5, 3, 8, 9, 2, 1, 7, 4, 5,
				2, 4, 7, 6, 12, 8, 1});
		Fork fork = new Fork(2);
		connect(source_values, fork);
		FunctionProcessor sum = new FunctionProcessor(Addition.instance);
		connect(fork, LEFT, sum, LEFT);
		Trim trim = new Trim(1);
		connect(fork, RIGHT, trim, INPUT);
		connect(trim, OUTPUT, sum, RIGHT);
		CountDecimate decimate = new CountDecimate(2);
		connect(sum, OUTPUT, decimate, INPUT);
		Pullable p = decimate.getPullableOutput();
		for (int i = 0; i < 9; i++)
		{
			int v = ((Number) p.pull()).intValue();
			System.out.printf("Event #%d is: %d\n", i, v);
		}
		
	}
}
