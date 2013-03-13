package edu.nyu.cascade.util;

import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.Writer;

import xtc.tree.Printer;

public class FlushingPrinter extends Printer {

  public FlushingPrinter(OutputStream arg0) {
    super(arg0);
  }

  public FlushingPrinter(PrintWriter arg0) {
    super(arg0);
  }

  public FlushingPrinter(Writer arg0) {
    super(arg0);
  }

  @Override
  public Printer pln() {
    return super.pln().flush();
  }

  @Override
  public Printer pln(char arg0) {
    return super.pln(arg0).flush();
  }

  @Override
  public Printer pln(double arg0) {
    return super.pln(arg0).flush();
  }

  @Override
  public Printer pln(int arg0) {
    return super.pln(arg0).flush();
  }

  @Override
  public Printer pln(long arg0) {
    return super.pln(arg0).flush();
  }

  @Override
  public Printer pln(String arg0) {
    return super.pln(arg0).flush();
  }
}
