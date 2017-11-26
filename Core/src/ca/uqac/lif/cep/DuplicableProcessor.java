package ca.uqac.lif.cep;

public interface DuplicableProcessor extends Duplicable
{
	@Override
	public Processor duplicate();
}