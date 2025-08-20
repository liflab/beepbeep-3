<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <!-- Map JDK number to Eclipse JRE container name -->
  <xsl:variable name="vmType"
    select="'org.eclipse.jdt.internal.debug.ui.launcher.StandardVMType'"/>
  <xsl:template name="jre-container">
    <xsl:param name="jdk"/>
    <xsl:text>org.eclipse.jdt.launching.JRE_CONTAINER/</xsl:text>
    <xsl:value-of select="$vmType"/>
    <xsl:text>/JavaSE-</xsl:text>
    <xsl:value-of select="$jdk"/>
  </xsl:template>
  
  <!-- Discover depdir -->
  <xsl:param name="depdir">
  <xsl:choose>
    <xsl:when test="/build/depdir">
      <xsl:value-of select="/build/depdir/text()"/>
    </xsl:when>
    <xsl:otherwise>Source/Core/dep</xsl:otherwise>
  </xsl:choose>
  </xsl:param>
  
  <!-- Discover srcdir -->
  <xsl:param name="srcdir">
  <xsl:choose>
    <xsl:when test="/build/srcdir">
      <xsl:value-of select="/build/srcdir/text()"/>
    </xsl:when>
    <xsl:otherwise>Source/Core/src</xsl:otherwise>
  </xsl:choose>
  </xsl:param>

  <xsl:output method="xml" indent="yes" encoding="UTF-8"/>
  
  <!-- Strip ?query and #fragment -->
  <xsl:template name="strip-query">
    <xsl:param name="s"/>
    <xsl:choose>
      <xsl:when test="contains($s, '?')">
        <xsl:value-of select="substring-before($s, '?')"/>
      </xsl:when>
      <xsl:when test="contains($s, '#')">
        <xsl:value-of select="substring-before($s, '#')"/>
      </xsl:when>
      <xsl:otherwise><xsl:value-of select="$s"/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- basename(..) for URL path -->
  <xsl:template name="basename">
    <xsl:param name="path"/>
    <xsl:choose>
      <xsl:when test="contains($path, '/')">
        <xsl:call-template name="basename">
          <xsl:with-param name="path" select="substring-after($path, '/')"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise><xsl:value-of select="$path"/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="/build">
    <classpath>

      <!-- Project-to-project deps -->
      <xsl:for-each select="dependencies/project">
        <classpathentry kind="src" path="/{normalize-space(.)}"/>
      </xsl:for-each>

      <!-- External JARs (URL -> depdir/basename.jar) -->
      <xsl:for-each select="dependencies/dependency[bundle='true']/files/jar">
        <xsl:variable name="clean">
          <xsl:call-template name="strip-query">
            <xsl:with-param name="s" select="text()"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="file">
          <xsl:call-template name="basename">
            <xsl:with-param name="path" select="$clean"/>
          </xsl:call-template>
        </xsl:variable>
        <classpathentry kind="lib" path="{$depdir}/{$file}" exported="true"/>
      </xsl:for-each>
      <xsl:for-each select="dependencies/dependency[bundle='false']/files/jar">
        <xsl:variable name="clean">
          <xsl:call-template name="strip-query">
            <xsl:with-param name="s" select="text()"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="file">
          <xsl:call-template name="basename">
            <xsl:with-param name="path" select="$clean"/>
          </xsl:call-template>
        </xsl:variable>
        <classpathentry kind="lib" path="{$depdir}/{$file}"/>
      </xsl:for-each>
      <xsl:for-each select="dependencies/dependency[bundle='true']/files/zip">
        <xsl:variable name="clean">
          <xsl:call-template name="strip-query">
            <xsl:with-param name="s" select="text()"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="file">
          <xsl:call-template name="basename">
            <xsl:with-param name="path" select="concat(substring($clean, 1, string-length($clean) - 4), '.jar')"/>
          </xsl:call-template>
        </xsl:variable>
        <classpathentry kind="lib" path="{$depdir}/{$file}" exported="true"/>
      </xsl:for-each>
      <xsl:for-each select="dependencies/dependency[bundle='false']/files/zip">
        <xsl:variable name="clean">
          <xsl:call-template name="strip-query">
            <xsl:with-param name="s" select="text()"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="file">
          <xsl:call-template name="basename">
            <xsl:with-param name="path" select="concat(substring($clean, 1, string-length($clean) - 4), '.jar')"/>
          </xsl:call-template>
        </xsl:variable>
        <classpathentry kind="lib" path="{$depdir}/{$file}"/>
      </xsl:for-each>

      <!-- Project dependencies: reference sibling projects by /Name -->
      <xsl:for-each select="dependencies/project">
        <classpathentry kind="src">
          <xsl:attribute name="path">
            <xsl:text>/</xsl:text><xsl:value-of select="."/>
          </xsl:attribute>
        </classpathentry>
      </xsl:for-each>

      <!-- JRE container -->
      <classpathentry kind="con">
        <xsl:attribute name="path">
          <xsl:call-template name="jre-container">
            <xsl:with-param name="jdk" select="normalize-space(targetjdk)"/>
          </xsl:call-template>
        </xsl:attribute>
      </classpathentry>

      <!-- Output -->
      <classpathentry kind="output">
        <xsl:attribute name="path">
          <xsl:value-of select="normalize-space(bindir)"/>
        </xsl:attribute>
      </classpathentry>
    </classpath>
  </xsl:template>

</xsl:stylesheet>