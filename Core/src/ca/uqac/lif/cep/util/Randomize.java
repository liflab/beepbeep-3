/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2018 Sylvain Hallé

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
package ca.uqac.lif.cep.util;

import ca.uqac.lif.cep.UniformProcessor;
import java.util.Random;

public class Randomize extends UniformProcessor
{
  /**
   * An instance of a random number generator
   */
  Random m_random;
  
  /**
   * The lower bound of the interval for the random
   * values to generate
   */
  float m_minValue;
  
  /**
   * The upper bound of the interval for the random
   * values to generate
   */
  float m_maxValue;
  
  /**
   * Creates a new Randomize processor
   * @param arity The input/output arity of this processor
   * @param min The lower bound of the interval for the random
   *   values to generate 
   * @param max The upper bound of the interval for the random
   *   values to generate 
   */
  public Randomize(int arity, float min, float max)
  {
    super(arity, arity);
    m_random = new Random();
    m_minValue = min;
    m_maxValue = max;
  }

  /**
   * Creates a new Randomize processor with an input/output arity of 1
   * @param min The lower bound of the interval for the random
   *   values to generate 
   * @param max The upper bound of the interval for the random
   *   values to generate 
   */
  public Randomize(float min, float max)
  {
    this(1, min, max);
  }
  
  /**
   * Sets the seed of the random number generator
   * @param seed The seed
   */
  public void setSeed(int seed)
  {
    m_random = new Random(seed);
  }

  @Override
  protected boolean compute(Object[] inputs, Object[] outputs)
  {
    for (int i = 0; i < getOutputArity(); i++)
    {
      outputs[i] = m_random.nextFloat() * (m_maxValue - m_minValue) + m_minValue;
    }
    return true;
  }

  @Override
  public Randomize duplicate(boolean with_state)
  {
    return new Randomize(getInputArity(), m_minValue, m_maxValue);
  }
}
