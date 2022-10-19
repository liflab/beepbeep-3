/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.functions.BinaryFunction;
import ca.uqac.lif.cep.functions.UnaryFunction;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A container object for string functions
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class Strings
{
  private Strings()
  {
    // Utility class
  }

  public static final Concat concat = new Concat();

  public static final Contains contains = new Contains();

  public static final EndsWith endsWith = new EndsWith();

  public static final Matches matches = new Matches();

  public static final StartsWith startsWith = new StartsWith();

  public static final ToString toString = ToString.instance;

  /**
   * Concatenates input strings into an output string
   */
  public static class BuildString extends UniformProcessor
  {
    /**
     * The string builder used to store the output string
     */
    protected StringBuilder m_builder;

    /**
     * An optional separator to insert after each string
     */
    protected String m_separator;

    /**
     * Creates a new build string processor
     */
    public BuildString()
    {
      super(1, 1);
      m_builder = new StringBuilder();
      m_separator = "";
    }

    public BuildString setSeparator(String separator)
    {
      m_separator = separator;
      return this;
    }

    @Override
    public void reset()
    {
      super.reset();
      m_builder = new StringBuilder();
      m_inputCount = 0;
    }

    @Override
    protected boolean compute(Object[] inputs, Object[] outputs)
    {
      if (m_inputCount > 0)
      {
        m_builder.append(m_separator);
      }
      m_builder.append(inputs[0].toString());
      outputs[0] = m_builder.toString();
      m_inputCount++;
      return true;
    }

    @Override
    public Processor duplicate(boolean with_state)
    {
      BuildString bs = new BuildString();
      bs.m_separator = m_separator;
      if (with_state)
      {
        bs.m_builder.append(m_builder.toString());
        bs.m_inputCount = m_inputCount;
      }
      return bs;
    }
  }

  /**
   * Concatenates two strings
   */
  public static class Concat extends BinaryFunction<Object, Object, String>
  {
    protected Concat()
    {
      super(Object.class, Object.class, String.class);
    }

    @Override
    public String getValue(Object s1, Object s2)
    {
      return s1.toString() + s2.toString();
    }
  }

  /**
   * Function that checks if a string contains another
   */
  public static class Contains extends BinaryFunction<String, String, Boolean>
  {
    public static final Contains instance = new Contains();

    protected Contains()
    {
      super(String.class, String.class, Boolean.class);
    }

    @Override
    public Boolean getValue(String s1, String s2)
    {
      return s1.contains(s2);
    }
  }

  /**
   * Function that checks if a string ends by another
   */
  public static class EndsWith extends BinaryFunction<String, String, Boolean>
  {
    public static final EndsWith instance = new EndsWith();

    protected EndsWith()
    {
      super(String.class, String.class, Boolean.class);
    }

    @Override
    public Boolean getValue(String s1, String s2)
    {
      return s1.endsWith(s2);
    }
  }

  /**
   * Checks if a string matches a regular expression
   */
  public static class Matches extends BinaryFunction<String, String, Boolean>
  {
    public static final Matches instance = new Matches();

    protected Matches()
    {
      super(String.class, String.class, Boolean.class);
    }

    @Override
    public Boolean getValue(String s1, String s2)
    {
      return s1.matches(s2);
    }
  }

  /**
   * Checks if a string starts by another
   */
  public static class StartsWith extends BinaryFunction<String, String, Boolean>
  {
    public static final StartsWith instance = new StartsWith();

    protected StartsWith()
    {
      super(String.class, String.class, Boolean.class);
    }

    @Override
    public Boolean getValue(String s1, String s2)
    {
      return s1.startsWith(s2);
    }
  }

  /**
   * Transforms a comma-separated line of text into an array
   * 
   * @author Sylvain Hallé
   */
  public static class SplitString extends UnaryFunction<String, Object>
  {
    /**
     * An instance of this function with default values
     */
    public static final transient SplitString instance = new SplitString(":");

    /**
     * The symbol used to separate data fields
     */
    protected String m_separator = ":";

    /**
     * Whether to trim each part of the string before processing
     */
    protected boolean m_trim = true;

    public SplitString(String separator)
    {
      super(String.class, Object.class);
      m_separator = separator;
    }

    /**
     * Sets whether to apply <tt>trim()</tt> to each substring
     * 
     * @param b
     *          Set to <tt>true</tt> to trim, <tt>false</tt> otherwise
     * @return This function
     */
    public SplitString trim(boolean b)
    {
      m_trim = b;
      return this;
    }

    @Override
    public Object getValue(String s)
    {
      String[] parts = s.split(m_separator);
      Object[] typed_parts = new Object[parts.length];
      for (int i = 0; i < parts.length; i++)
      {
        if (m_trim)
        {
          typed_parts[i] = createConstantFromString(parts[i].trim());
        }
        else
        {
          typed_parts[i] = createConstantFromString(parts[i]);
        }
      }
      return typed_parts;
    }

    /**
     * Attempts to create a constant based on the contents of a string. That is, if
     * the string contains only digits, it will create an number instead of a
     * string.
     * 
     * @param s
     *          The string to read from
     * @return The constant
     */
    public static Object createConstantFromString(String s)
    {
      try
      {
        return Integer.parseInt(s);
      }
      catch (NumberFormatException nfe1)
      {
        try
        {
          return Float.parseFloat(s);
        }
        catch (NumberFormatException nfe2)
        {
          // Do nothing
        }
      }
      // This is a string
      return s;
    }
  }

  /**
   * Transforms any object into a string using the "toString" method.
   */
  public static class ToString extends UnaryFunction<Object, String>
  {
    public static final transient ToString instance = new ToString();

    private ToString()
    {
      super(Object.class, String.class);
    }

    @Override
    public String getValue(Object x)
    {
      return x.toString();
    }
  }

  /**
   * Finds all substrings that match capturing group 1 of a regular expression.
   * @author Sylvain Hallé
   */
  @SuppressWarnings("rawtypes")
  public static class FindRegex extends UnaryFunction<String, Set>
  {
    /**
     * The regular expression to look for
     */
    protected String m_regex;

    /**
     * The pattern object compiled from this regular expression
     */
    protected transient Pattern m_pattern;

    /**
     * Creates a new FindRegex function
     * @param regex The regular expression this function is expected to find
     */
    public FindRegex(String regex)
    {
      super(String.class, Set.class);
      m_regex = regex;
      m_pattern = Pattern.compile(regex);
    }

    @Override
    public Set getValue(String s)
    {
      Matcher mat = m_pattern.matcher(s);
      Set<String> set = new HashSet<String>();
      while (mat.find())
      {
        set.add(mat.group(1));
      }
      return set;
    }
  }
}
