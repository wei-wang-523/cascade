package edu.nyu.cascade.control;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

import edu.nyu.cascade.control.jaxb.ControlFile.Theory;
import edu.nyu.cascade.prover.ExpressionManager;


public class TheoryId {
  public static TheoryId valueOf(Theory theory) {
    return new TheoryId(theory.getQname());
  }
  
  public edu.nyu.cascade.c.Theory getInstance(ExpressionManager exprManager) 
  throws ControlFileException {
    try {
      Class<?> theoryClass = Class.forName(qname);
      Constructor<?> theoryConstr = theoryClass.getConstructor(ExpressionManager.class);
      return (edu.nyu.cascade.c.Theory) theoryConstr.newInstance(exprManager);
    } catch (ClassNotFoundException e) {
      throw new ControlFileException(e);
    } catch (SecurityException e) {
      throw new ControlFileException(e);
    } catch (NoSuchMethodException e) {
      throw new ControlFileException(e);
    } catch (IllegalArgumentException e) {
      throw new ControlFileException(e);
    } catch (InstantiationException e) {
      throw new ControlFileException(e);
    } catch (IllegalAccessException e) {
      throw new ControlFileException(e);
    } catch (InvocationTargetException e) {
      throw new ControlFileException(e);
    }
  }
  
  private final String qname;
  
  public TheoryId(String qname) { this.qname = qname; }
  public String getQname() { return qname; }
}
