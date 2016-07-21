package ca.uqac.lif.cep.xml;

import java.util.Collection;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.xml.XPathExpression;
import ca.uqac.lif.xml.XmlElement;

/**
 * Utility function to evaluate an XPath expression, ending with 
 * a <code>text()</code> element
 */
public abstract class XPathFunctionGet<T> extends UnaryFunction<XmlElement,T>
{	
	/**
	 * The expression to evaluate
	 */
	protected XPathExpression m_expression;
	
	public XPathFunctionGet(String exp, Class<T> clazz)
	{
		super(XmlElement.class, clazz);
		m_expression = XPathFunction.parseExpression(exp);
	}
	
	public XPathFunctionGet(XPathExpression exp, Class<T> clazz)
	{
		super(XmlElement.class, clazz);
		m_expression = exp;
	}

	@Override
	public T getValue(XmlElement x)
	{
		Collection<XmlElement> col = m_expression.evaluate(x);
		for (XmlElement xe : col)
		{
			return castValue(xe);
		}
		return null;
	}
	
	public abstract T castValue(XmlElement e);
	
	@Override
	public void setContext(Context context)
	{
		m_expression = XPathFunction.evaluatePlaceholders(m_expression, context);
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		Context con = new Context();
		con.put(key, value);
		m_expression = XPathFunction.evaluatePlaceholders(m_expression, con);
	}
	
	@Override
	public String toString()
	{
		return m_expression.toString();
	}
}