/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2026 Sylvain Hallé

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

import static org.junit.Assert.assertTrue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.EventAt;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Utilities;
import ca.uqac.lif.petitpoucet.Assertions;
import ca.uqac.lif.petitpoucet.CompositePart;
import ca.uqac.lif.petitpoucet.circuit.Connectable.InputPart;
import ca.uqac.lif.petitpoucet.circuit.Connectable.OutputPart;
import ca.uqac.lif.petitpoucet.Explainable.ExplanationException;
import ca.uqac.lif.petitpoucet.IdentityVertexFactory;
import ca.uqac.lif.petitpoucet.Vertex;
import ca.uqac.lif.petitpoucet.VertexFactory;

import java.util.Queue;
import org.junit.Test;

/**
 * Unit tests for the {@link Trim} processor.
 * @author Sylvain Hallé
 */
public class TrimTest
{
  @Test
  public void testTrim() 
  {
    Trim d = new Trim(3);
    QueueSink qs = new QueueSink(1);
    Connector.connect(d, qs);
    Pushable in = d.getPushableInput(0);
    Queue<Object> queue = qs.getQueue(0);
    for (int k = 0; k < 2; k++)
    {
      in.push(0);
      assertTrue(queue.isEmpty());
      in.push(1);
      assertTrue(queue.isEmpty());
      in.push(2);
      assertTrue(queue.isEmpty());
      in.push(3);
      Utilities.queueContains(3, queue);
      in.push(4);
      Utilities.queueContains(4, queue);
      d.reset();
    }
  }
  
  @Test
  public void testExplain1() throws ExplanationException
  {
  	Trim d = new Trim(3);
  	Vertex e = d.explain(CompositePart.compose(new EventAt(0), new OutputPart(0)));
  	VertexFactory f = new IdentityVertexFactory();
  	Assertions.assertEqualGraphs(e, f.getPart(CompositePart.compose(new EventAt(3), new InputPart(0)), d));
  }
  
  @Test
  public void testExplain2() throws ExplanationException
  {
  	// The idea of this test is to make sure that the tail of p is preserved
  	Trim d = new Trim(3);
  	Vertex e = d.explain(CompositePart.compose(new EventAt(10), new EventAt(0), new OutputPart(0)));
  	VertexFactory f = new IdentityVertexFactory();
  	Assertions.assertEqualGraphs(e, f.getPart(CompositePart.compose(new EventAt(10), new EventAt(3), new InputPart(0)), d));
  }
}
