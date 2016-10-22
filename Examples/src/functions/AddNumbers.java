package functions;

import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.numbers.Addition;

public class AddNumbers
{
	public static void main(String[] args)
	{
		// SNIP
		Function add = Addition.instance;
		Object[] inputs = new Object[]{2, 3};
		Object values[] = add.evaluate(inputs);
		float value = (Float) values[0];
		System.out.printf("The value is %f\n", value);
		// SNIP
	}
}
