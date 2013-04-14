<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns="http://www.w3.org/1999/xhtml">
  <xsl:output method="xml" indent="yes" omit-xml-declaration="yes" doctype-public="-//W3C//DTD XHTML 1.0 Strict//EN" doctype-system="http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd"/>
  <xsl:template match="/">
    <html xml:lang="fr">
      <head>
        <title>Slimmer - BATT - Parsifal - Bedwyr</title>

        <link rel="shortcut icon" type="image/x-icon" href="img/bedwyr.ico"/>
        <link rel="stylesheet" type="text/css" href="skeleton.css" title="Bedwyr 1.4"/>
        <meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
      </head>
      <body>
        <xsl:apply-templates select="skeleton"/>
      </body>
    </html>
  </xsl:template>
  <xsl:template match="skeleton">
    <div class="skeleton">
      <xsl:apply-templates/>
    </div>
  </xsl:template>
  <xsl:template match="son">
    <div>
      <span class="atom {@value}" id="atom{@id}">
        <xsl:value-of select="atom"/>
      </span>
    </div>
    <div class="proof">
      <xsl:apply-templates select="son|loop|cut"/>
    </div>
  </xsl:template>
  <xsl:template match="loop">
    <div>
      <span class="atom loop status{@value}">
        <a href="#atom{@ref}"><xsl:value-of select="."/></a>
      </span>
    </div>
  </xsl:template>
  <xsl:template match="cut">
    <div>
      <span class="atom cut status{@value}">
        <a href="#atom{@ref}"><xsl:value-of select="."/></a>
      </span>
    </div>
  </xsl:template>
</xsl:stylesheet>
