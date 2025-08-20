<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <xsl:output method="xml" indent="yes" encoding="UTF-8"/>

  <xsl:template match="/build">
    <projectDescription>
      <name><xsl:value-of select="normalize-space(name)"/></name>
      <comment></comment>
      <projects/>   <!-- (Optional) referenced projects here is not required when using classpath deps -->
      <buildSpec>
        <buildCommand>
          <name>org.eclipse.jdt.core.javabuilder</name>
          <arguments/>
        </buildCommand>
      </buildSpec>
      <natures>
        <nature>org.eclipse.jdt.core.javanature</nature>
      </natures>
    </projectDescription>
  </xsl:template>
</xsl:stylesheet>

