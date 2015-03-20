package ca.uqac.lif.cep;

/**
 * Provides a number of convenient methods for connecting the outputs of
 * processors to the inputs of other processors.
 * @author sylvain
 *
 */
public class Connector
{
	/**
	 * Connects the <i>i</i>-th output of <tt>p1</tt> to the
	 * <i>j</i>-th input of <tt>p2</tt>
	 * @param p1 The first processor
	 * @param p2 The second processor
	 * @param i The output number of the first processor
	 * @param j The input number of the second processor
	 */
	public static void connect(Processor p1, Processor p2, int i, int j)
	{
		// Pull
		Pullable p1_out = p1.getPullableOutput(i);
		p2.setPullableInput(j, p1_out);
		// Push
		Pushable p2_in = p2.getPushableInput(j);
		p1.setPushableOutput(i, p2_in);
	}
	
	/**
	 * Connects two processors, by associating the <i>-th output of <tt>p1</tt>
	 * to the <i>-th input of <tt>p2</tt>
	 * @param p1 The first processor
	 * @param p2 The second processor
	 */
	public static void connect(Processor p1, Processor p2)
	{
		int arity = p1.getOutputArity();
		for (int i = 0; i < arity; i++)
		{
			connect(p1, p2, i, i);
		}
	}
	
	/**
	 * Connects three processors, by associating the (first) output of <tt>p1</tt>
	 * and <tt>p2</tt> respectively to the first and second input of <tt>p3</tt>
	 * @param p1 The first processor
	 * @param p2 The second processor
	 */
	public static void connect(Processor p1, Processor p2, Processor p3)
	{
		connect(p1, p3, 0, 0);
		connect(p2, p3, 0, 1);
	}
}
