package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.Duplicable;

public interface DuplicableFunction extends Duplicable
{
  @Override
  public Function duplicate();
}