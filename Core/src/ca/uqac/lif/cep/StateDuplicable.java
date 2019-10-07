package ca.uqac.lif.cep;

public interface StateDuplicable<T> extends Duplicable<T>
{
	public T duplicate(boolean with_state);
}
