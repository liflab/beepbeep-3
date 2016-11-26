package ca.uqac.lif.cep.concurrency;

public class ThreadManager 
{
	public static void sleep(long duration)
	{
		try
		{
			Thread.sleep(duration);
		}
		catch (InterruptedException e)
		{
			// Do nothing
		}		
	}
}
