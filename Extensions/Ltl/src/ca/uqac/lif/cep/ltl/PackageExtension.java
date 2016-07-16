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
package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.FileHelper;
import ca.uqac.lif.cep.interpreter.Palette;

public class PackageExtension extends Palette
{
	public PackageExtension()
	{
		super(PackageExtension.class, "Linear Temporal Logic palette\n"
				+ "(C) 2015-2016 Sylvain Hallé, Université du Québec à Chicoutim");
		add(new PaletteEntry("And", And.class, FileHelper.internalFileToBytes(PackageExtension.class, "And.png")));
		add(new PaletteEntry("Or", Or.class, FileHelper.internalFileToBytes(PackageExtension.class, "Or.png")));
		add(new PaletteEntry("Next", Next.class, FileHelper.internalFileToBytes(PackageExtension.class, "Next.png")));
		add(new PaletteEntry("Not", Not.class, FileHelper.internalFileToBytes(PackageExtension.class, "Not.png")));
		add(new PaletteEntry("Eventually", Eventually.class, FileHelper.internalFileToBytes(PackageExtension.class, "Eventually.png")));
		add(new PaletteEntry("Globally", Eventually.class, FileHelper.internalFileToBytes(PackageExtension.class, "Globally.png")));
	}
}
