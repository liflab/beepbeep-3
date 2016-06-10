/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Random;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.eml.tuples.EmlNumber;
import ca.uqac.lif.cep.eml.tuples.EmlString;
import ca.uqac.lif.cep.eml.tuples.NamedTuple;
import ca.uqac.lif.cep.eml.tuples.TupleGrammar;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.io.StreamGrammar;
import ca.uqac.lif.parkbench.Benchmark;
import ca.uqac.lif.parkbench.Parameters;
import ca.uqac.lif.parkbench.Test;
import ca.uqac.lif.parkbench.TestSuite;
import ca.uqac.lif.parkbench.plot.ScatterPlot;


public class StockTest1 extends TestSuite
{
	public static void main(String[] args)
	{
		initialize(args, new StockTest1());
	}

	@Override
	public void setup(Benchmark b)
	{
		for (int num_stocks = 5; num_stocks < 1000; num_stocks += 100)
		{
			for (int num_timestamps = 100; num_timestamps < 10000; num_timestamps += 1000)
			{
				RandomStockTest rst = new RandomStockTest();
				rst.setParameter("num-stocks", num_stocks);
				rst.setParameter("num-timestamps", num_timestamps);
				b.addTest(rst);
			}
		}
		ScatterPlot plot = new ScatterPlot("Throughput").withLines();
		plot.setParameterX("num-timestamps", "Number of events").setParameterY("throughput", "Throughput (events/s)");
		plot.addTests(b);
		b.addPlot(plot);
	}

	public static class RandomStockTest extends Test
	{
		public RandomStockTest()
		{
			super("Random stocks");
		}

		@Override
		public Test newTest()
		{
			return new RandomStockTest();
		}

		@Override
		public void runTest(Parameters input, Parameters output)
		{
			int num_timestamps = input.getNumber("num-timestamps").intValue();
			int num_stocks = input.getNumber("num-stocks").intValue();
			Pullable p = setupQuery(num_stocks);
			long time_start = System.nanoTime();
			for (int i = 0; i < num_timestamps; i++)
			{
				/* EmlNumber dummy = (EmlNumber) */ p.pullHard();
			}
			long time_end = System.nanoTime();
			long duration_ms = (time_end - time_start) / (long) 1000000f;
			output.put("time", duration_ms);
			output.put("throughput", (num_timestamps * num_stocks * 1000) / duration_ms);
			stopWithStatus(Status.DONE);
		}

		public Pullable setupQuery(int num_stocks)
		{
			Interpreter my_int = new Interpreter();
			// Import grammar extensions for I/O
			my_int.extendGrammar(StreamGrammar.class);
			// Import grammar extensions for tuples
			my_int.extendGrammar(TupleGrammar.class);

			// Add a few definitions
			my_int.executeQuery("WHEN @P IS A processor: THE COUNT OF ( @P ) IS THE processor COMBINE (SELECT 1 FROM (@P)) WITH SUM");
			my_int.executeQuery("WHEN @P IS A processor: THE SUM OF ( @P ) IS THE processor COMBINE (@P) WITH SUM");
			my_int.executeQuery("WHEN @P IS A processor: THE AVERAGE OF ( @P ) IS THE processor SELECT (T.x) ÷ (U.x) FROM (THE SUM OF (@P) AS T, THE COUNT OF (@P) AS U)");

			// Name the input trace
			my_int.executeQuery("ClosingStockPrices IS THE processor @T");
			my_int.addPlaceholder("@T", "processor", new RandomStockData(num_stocks));

			// Read tuples from a file
			Pullable result = my_int.executeQuery("EVERY 5TH OF (APPLY (THE AVERAGE OF (0)) ON (SELECT closingPrice FROM (((SELECT closingPrice, stockSymbol FROM (ClosingStockPrices)) WHERE (stockSymbol) = (\"1\")))) ON A WINDOW OF 5)");
			return result;
		}
	}

	public static class RandomStockData extends SingleProcessor
	{
		protected Set<String> m_stockSymbols;

		protected int m_timestamp;

		protected Random m_random;

		public RandomStockData(int num_symbols)
		{
			super(0, 1);
			m_stockSymbols = new HashSet<String>();
			for (int i = 0; i < num_symbols; i++)
			{
				// Fill set with dummy stock symbols
				m_stockSymbols.add(new Integer(i).toString());
			}
			m_timestamp = 0;
			m_random = new Random();
		}

		@Override
		protected Queue<Vector<Object>> compute(Vector<Object> inputs)
		{
			// Generate the next batch of tuples
			Queue<Vector<Object>> out_queue = new LinkedList<Vector<Object>>();
			for (String symbol : m_stockSymbols)
			{
				NamedTuple nt = new NamedTuple();
				int value = m_random.nextInt(1000);
				nt.put("stockSymbol", new EmlString(symbol));
				nt.put("closingPrice", new EmlNumber(value));
				nt.put("closingPrice", new EmlNumber(m_timestamp));
				Vector<Object> vo = new Vector<Object>();
				vo.add(nt);
				out_queue.add(vo);
			}
			m_timestamp++;
			return out_queue;
		}

		@Override
		public void build(Stack<Object> stack)
		{
			// Nothing to do
		}

	}

}
