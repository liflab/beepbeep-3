/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2025 Sylvain Hallé

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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.EventAt;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Utilities;
import ca.uqac.lif.petitpoucet.Assertions;
import ca.uqac.lif.petitpoucet.CompositePart;
import ca.uqac.lif.petitpoucet.Vertex;
import ca.uqac.lif.petitpoucet.VertexFactory;
import ca.uqac.lif.petitpoucet.circuit.Connectable.InputPart;
import ca.uqac.lif.petitpoucet.circuit.Connectable.OutputPart;
import ca.uqac.lif.petitpoucet.Explainable.ExplanationException;
import ca.uqac.lif.petitpoucet.IdentityVertexFactory;

import java.util.Queue;
import org.junit.Test;

/**
 * Unit tests for the {@link CountDecimate} processor.
 * @author Sylvain Hallé
 */
public class CountDecimateTest
{
  @Test
  public void testCountDecimate1() 
  {
    CountDecimate f = new CountDecimate(3);
    QueueSink qs = new QueueSink(1);
    Connector.connect(f, qs);
    Pushable in = f.getPushableInput(0);
    Queue<Object> queue = qs.getQueue(0);
    for (int k = 0; k < 2; k++)
    {
      in.push(0);
      assertEquals(1, queue.size());
      Utilities.queueContains(0, queue);
      in.push(1);
      assertTrue(queue.isEmpty());
      in.push(2);
      assertTrue(queue.isEmpty());
      in.push(3);
      Utilities.queueContains(3, queue);
      in.push(4);
      assertTrue(queue.isEmpty());
      in.push(5);
      assertTrue(queue.isEmpty());
      in.push(6);
      Utilities.queueContains(6, queue);
      f.reset();
    }
  }

  @Test
  public void testCountDecimate2() 
  {
    CountDecimate f = new CountDecimate();
    QueueSink qs = new QueueSink(1);
    Connector.connect(f, qs);
    Pushable in = f.getPushableInput(0);
    Queue<Object> queue = qs.getQueue(0);
    for (int k = 0; k < 2; k++)
    {
      in.push(0);
      assertEquals(1, queue.size());
      Utilities.queueContains(0, queue);
      in.push(1);
      Utilities.queueContains(1, queue);
      in.push(2);
      Utilities.queueContains(2, queue);
      f.reset();
    }
  }
  
  @Test
  public void testExplain1() throws ExplanationException
  {
  	CountDecimate d = new CountDecimate(3);
  	Vertex e = d.explain(CompositePart.compose(new EventAt(0), new OutputPart(0)));
  	VertexFactory f = new IdentityVertexFactory();
  	Assertions.assertEqualGraphs(e, f.getPart(CompositePart.compose(new EventAt(0), new InputPart(0)), d));
  }
  
  @Test
  public void testExplain2() throws ExplanationException
  {
  	CountDecimate d = new CountDecimate(3);
  	Vertex e = d.explain(CompositePart.compose(new EventAt(1), new OutputPart(0)));
  	VertexFactory f = new IdentityVertexFactory();
  	Assertions.assertEqualGraphs(e, f.getPart(CompositePart.compose(new EventAt(3), new InputPart(0)), d));
  }
}
