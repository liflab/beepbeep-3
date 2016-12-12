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
package ca.uqac.lif.cep;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

/**
 * Visits every processor
 * @author Sylvain Hallé
 */
public abstract class PipeCrawler 
{
	/**
	 * The maximum number of loops that the crawler can do during a traversal.
	 * This is intended as a safety measure to make sure that method
	 * {@link #crawl(Processor)} always terminates.
	 */
	protected static final transient int s_maxCrawls = 10000;
	
	/**
	 * Crawls a graph from some starting point
	 * @param start
	 */
	public synchronized void crawl(Processor start)
	{
		Queue<Processor> to_visit = new LinkedList<Processor>();
		Set<Processor> visited = new HashSet<Processor>();
		to_visit.add(start);
		/*
		 * This is actually while(!to_visit.isEmpty()), whose number of iterations
		 * is bounded by s_maxCrawls for safety.
		 */
		for (int num_crawls = 0; num_crawls < s_maxCrawls && !to_visit.isEmpty(); num_crawls++)
		{
			Processor proc = to_visit.remove();
			visit(proc);
			visited.add(proc);
			int in_arity = proc.getInputArity();
			int out_arity = proc.getOutputArity();
			for (int i = 0; i < out_arity; i++)
			{
				//Pushable p = proc.getPushableInput(i);
				Pushable p = proc.getPushableOutput(i);
				if (p != null)
				{
					Processor target = p.getProcessor();
					if (!to_visit.contains(target) && !visited.contains(target))
					{
						to_visit.add(target);
					}
				}
			}
			for (int i = 0; i < in_arity; i++)
			{
				Pullable p = proc.getPullableInput(i);
				//Pullable p = proc.getPullableOutput(i);
				if (p != null)
				{
					Processor target = p.getProcessor();
					if (!to_visit.contains(target) && !visited.contains(target))
					{
						to_visit.add(target);
					}
				}
			}
		}
	}
	
	/**
	 * Do something on a processor. Upon a call to {@link #crawl(Processor)},
	 * this method is called exactly once for every reachable processor in the
	 * pipe graph.
	 * @param p A processor
	 */
	public abstract void visit(Processor p);
}
