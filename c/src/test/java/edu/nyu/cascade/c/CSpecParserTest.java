package edu.nyu.cascade.c;

import static junit.framework.Assert.assertEquals;

import java.io.IOException;
import java.io.StringReader;

import org.junit.Test;

import edu.nyu.cascade.c.CSpecParser;

import xtc.parser.ParseException;
import xtc.parser.Result;
import xtc.tree.Node;


public class CSpecParserTest {
  @Test
  public void testSpecWithUCharCast() throws IOException, ParseException {
    /* TODO: Should check that the parser consumes the entire input. Can't figure out where to get this. [chris 5/19/2009] */
  CSpecParser specParser = new CSpecParser(new StringReader(
        "p != (unsigned char *) &cp && p != &n"), "foo");
    Result specResults = specParser.pCSpecExpression(0);
    Node spec = (Node) specParser.value(specResults);
    assertEquals("LogicalAndExpression", spec.getName());
  }

  
  @Test(expected=ParseException.class)
  public void testSpecWithUint8Cast() throws IOException, ParseException {
    /*
     * TODO: This fails because the parser doesn't know about uint8_t without
     * the inclusion of stdint.h. Is there some way to invoke the pre-processor
     * without turning the expression into a translation unit? Or should we embed
     * the expression in a specially named entity within a temp file, parse the whole
     * thing, then extract this bit? [chris 5/19/2009]
     */
  CSpecParser specParser = new CSpecParser(new StringReader(
        "p != (uint8_t *) &cp && p != &n"), "foo");
    Result specResults = specParser.pCSpecExpression(0);
    Node spec = (Node) specParser.value(specResults);
    assertEquals("LogicalAndExpression", spec.getName());
  }

  @Test(expected=ParseException.class)
  public void testMalformedSpec() throws IOException, ParseException {
  CSpecParser specParser = new CSpecParser(new StringReader(
        "p != 0 p != 1"), "foo");
    Result specResults = specParser.pCSpecExpression(0);
    specParser.value(specResults);
  }

  public void testWellFormedSpec() throws IOException, ParseException {
  CSpecParser specParser = new CSpecParser(new StringReader(
        "p != 0 && p != 1"), "foo");
    Result specResults = specParser.pCSpecExpression(0);
    specParser.value(specResults);
  }

}
