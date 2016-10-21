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
package queries;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.tmf.Fork;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Trim;
import static ca.uqac.lif.cep.Connector.connect;
import static ca.uqac.lif.cep.Connector.INPUT;
import static ca.uqac.lif.cep.Connector.LEFT;
import static ca.uqac.lif.cep.Connector.OUTPUT;
import static ca.uqac.lif.cep.Connector.RIGHT;

/**
 * Calculates the Euclidean distance of each two successive points in an
 * input trace of (x,y) coordinates.
 *  
 * @author Sylvain Hallé
 *
 */
public class PointDistance 
{
	/*
	 * We create a new type of event: Point. A point is just
	 * an "x" and an "y" value.
	 */
	public static class Point
	{
		public float x;
		public float y;
		
		public Point(float x, float y)
		{
			this.x = x;
			this.y = y;
		}
	}
	
	/*
	 * We create a new function: Distance. This function takes two points
	 * as its input, and returns their Euclidean distance as its output.
	 * It is therefore a 2:1 function.
	 */
	public static class Distance extends BinaryFunction<Point,Point,Float>
	{
		public Distance()
		{
			super(Point.class, Point.class, Float.class);
		}

		@Override
		public Float getValue(Point p1, Point p2)
		{
			return (float) Math.sqrt(Math.pow(p1.x - p2.x, 2) + Math.pow(p1.y - p2.y, 2));
		}
	}
	
	public static void main(String[] args) throws ConnectorException
	{
		QueueSource point_source = new QueueSource(1);
		point_source.setEvents(getListOfPoints());
		Fork fork = new Fork(2);
		connect(point_source, OUTPUT, fork, INPUT);
		FunctionProcessor distance_proc = new FunctionProcessor(new Distance());
		connect(fork, LEFT, distance_proc, LEFT);
		Trim trim = new Trim(1);
		connect(fork, RIGHT, trim, INPUT);
		connect(trim, OUTPUT, distance_proc, RIGHT);
		
		// Pull and print the first 10 events from the output
		Pullable p = distance_proc.getPullableOutput(OUTPUT);
		for (int i = 0; i < 10; i++)
		{
			float d = (float) p.pull();
			System.out.println(d);
		}
	}
	
	/**
	 * Creates a dummy array of points
	 * @return An array of points
	 */
	public static Object[] getListOfPoints()
	{
		return new Object[]{
				new Point(2, 7),
				new Point(1, 8),
				new Point(2, 8),
				new Point(1, 8),
				new Point(2, 8),
				new Point(4, 5),
				new Point(9, 0),
				new Point(4, 5),
				new Point(2, 3),
				new Point(5, 3),
				new Point(6, 0),
				new Point(2, 8)
		};
	}
}
