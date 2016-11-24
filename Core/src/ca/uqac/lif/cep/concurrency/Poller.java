package ca.uqac.lif.cep.concurrency;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.NextStatus;

public interface Poller extends Runnable
{
	public static enum Call {NONE, HAS_NEXT, HAS_NEXT_SOFT, PULL, PULL_SOFT};
	
	public boolean isDone();
	
	public void call(Call c);
	
	public NextStatus getNextSoftStatus();
	
	public boolean getNextHardStatus();
	
	public Object getNextSoft();
	
	public Object getNextHard();
	
	public void stop();
	
	public Pullable getPullable();
	
}
