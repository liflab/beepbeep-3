/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2021 Sylvain Hallé

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

/**
 * A dummy main file defining a few system-wide constants.
 * @author Sylvain Hallé
 * @since 0.8
 */
public class Main
{
  /**
   * Major version number
   */
  public static final int s_majorVersion = 0;

  /**
   * Minor version number
   */
  public static final int s_minorVersion = 10;

  /**
   * Revision version number
   */
  public static final int s_revisionVersion = 5;

  private Main()
  {
    super();
  }

  /**
   * A "dummy" main method that only displays a simple message and terminates.
   * 
   * @param args
   *          Command-line arguments (all ignored)
   */
  public static void main(String[] args)
  {
    System.out.println("BeepBeep 3 v" + formatVersion() + " - An event stream processing engine");
    System.out.println("(C) 2008-2021 Laboratoire d'informatique formelle");
    System.out.println("Université du Québec à Chicoutimi, Canada");
    System.exit(0);
  }

  /**
   * Formats the version number. The function takes the major, minor and
   * revision number and creates a pretty-printed version of these numbers.
   * @return A formatted version number
   */
  private static String formatVersion()
  {
    String out = "" + s_majorVersion + "." + s_minorVersion;
    if (s_revisionVersion > 0)
    {
      out += "." + s_revisionVersion;
    }
    return out;
  }
}
