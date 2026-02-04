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
package ca.uqac.lif.cep;

/**
 * An object carrying a {@link Processor} to be connected, and which expects
 * a call to its {@link #call()} method after the connection is established.
 * Currently the only use of this object is discussed in detail in
 * {@link GroupProcessor#out(Processor)}.
 * @see GroupProcessor#out(Processor)
 * @author Sylvain Hallé
 * @since 0.11.4
 */
public interface CallAfterConnect
{
	/**
	 * Gets the processor carried by this object.
	 * @return The processor
	 */
	public Processor getProcessor();
	
	/**
	 * Performs whatever action is needed after the connection is established.
	 */
	public void call();
	
	/**
	 * A {@link CallAfterConnect} object that starts a processor after it has
	 * been connected to its input. In a Groovy script, this object spares the
	 * user from manually calling the {@link Processor#start()} method after
	 * connecting the last processor in the chain, in order for it to start
	 * processing events.
	 */
	public static class StartAfterConnect implements CallAfterConnect
	{
		/**
		 * The processor to connect.
		 */
		private final Processor m_processor;
		
		/**
		 * Creates a new instance of the call.
		 * @param p The processor to connect
		 */
		public StartAfterConnect(Processor p)
		{
			super();
			m_processor = p;
		}
		
		@Override
		public Processor getProcessor()
		{
			return m_processor;
		}

		@Override
		public void call()
		{
			m_processor.start();
		}
	}
	
	/**
	 * A {@link RunAfterConnect} object that starts a {@link Runnable}
	 * processor after it has been connected to its input.
	 */
	public static class RunAfterConnect implements CallAfterConnect
	{
		/**
		 * The processor to connect.
		 */
		private final Processor m_processor;
		
		/**
		 * Creates a new instance of the call.
		 * @param p The processor to connect
		 */
		public RunAfterConnect(Processor p)
		{
			super();
			m_processor = p;
		}
		
		@Override
		public Processor getProcessor()
		{
			return m_processor;
		}

		@Override
		public void call()
		{
			((Runnable) m_processor).run();
		}
	}
}
