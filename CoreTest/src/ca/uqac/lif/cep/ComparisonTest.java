package ca.uqac.lif.cep;

import org.junit.Test;

import ca.uqac.lif.cep.functions.ApplyFunction;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.TurnInto;
import ca.uqac.lif.cep.tmf.Fork;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Window;
import ca.uqac.lif.cep.util.Numbers;

public class ComparisonTest
{
	@SuppressWarnings("unused")
  @Test
	public void test4()
	{
		int num_events = 100000;
		QueueSource src1 = new QueueSource().setEvents(0, 1, 2, 3, 4);
		src1.loop(true);
		Window win = new Window(new Cumulate(new CumulativeFunction<Number>(Numbers.addition)), 50);
		Connector.connect(src1, win);
		//win.setExecutorService(Executors.newSingleThreadExecutor());
		Pullable p = win.getPullableOutput();
		long time_start = System.currentTimeMillis();
		for (int i = 0; i < num_events; i++)
		{
			boolean b = p.hasNext();
			Object o = p.next();
		}
		long time_end = System.currentTimeMillis();
		System.out.println(1000 * num_events / (time_end - time_start));
	}
	
	@Test
	public void testRunningAverage1()
	{
		GroupProcessor gp0 = new GroupProcessor(1, 1);
		{
			Fork f = new Fork();
			gp0.associateInput(0, f, 0);
			Processor last = f;
			for (int i = 0; i < 10; i++)
			{
				Passthrough pt = new Passthrough();
				Connector.connect(last, 0, pt, 0);
				last = pt;
			}
			Cumulate sum = new Cumulate(new CumulativeFunction<Number>(Numbers.addition));
			Connector.connect(last, 0, sum, 0);
			TurnInto one = new TurnInto(1);
			Connector.connect(f, 1, one, 0);
			Cumulate sum_one = new Cumulate(new CumulativeFunction<Number>(Numbers.addition));
			Connector.connect(one, sum_one);
			ApplyFunction div = new ApplyFunction(Numbers.division);
			Connector.connect(sum, 0, div, 0);
			Connector.connect(sum_one, 0, div, 1);
			gp0.associateOutput(0, div, 0);
			gp0.addProcessors(f, sum, one, sum_one, div);
		}
		QueueSource src = new QueueSource().setEvents(1).loop(true);
		Connector.connect(src, gp0);
		Pullable p = gp0.getPullableOutput();
		long time_start = System.currentTimeMillis();
		for (int i = 0; i < 1000000; i++)
		{
			p.hasNext();
			p.pull();
		}
		System.out.println(System.currentTimeMillis() - time_start);
	}
}
