package ca.uqac.lif.cep.concurrency;

import ca.uqac.lif.cep.Pushable;

public interface Pusher extends Runnable
{
	public static enum Call {NONE, PUSH};
	
	public void waitFor();
	
	public void call(Call c);
		
	public void stop();
	
	public Pushable getPushable();
	
	public void setEventToPush(Object o);

}
