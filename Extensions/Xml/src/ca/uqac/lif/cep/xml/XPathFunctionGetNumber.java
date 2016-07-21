package ca.uqac.lif.cep.xml;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.xml.TextElement;
import ca.uqac.lif.xml.XPathExpression;
import ca.uqac.lif.xml.XmlElement;

/**
 * Utility function to evaluate an XPath expression, ending with 
 * a <code>text()</code> element
 */
public class XPathFunctionGetNumber extends XPathFunctionGet<Number>
{	
	public XPathFunctionGetNumber(String exp)
	{
		super(exp, Number.class);
	}
	
	public XPathFunctionGetNumber(XPathExpression exp)
	{
		super(exp, Number.class);
	}

	@Override
	public Number castValue(XmlElement e)
	{
		if (e instanceof TextElement)
		{
			return Float.parseFloat(((TextElement) e).getText());
		}
		return 0;
	}
	
	@Override
	public XPathFunctionGetNumber clone(Context context)
	{
		XPathExpression exp = XPathFunction.evaluatePlaceholders(m_expression, context);
		XPathFunctionGetNumber out = new XPathFunctionGetNumber(exp);
		return out;
	}
}