package edu.nyu.cascade.prover;

import java.io.File;
import java.io.FileFilter;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.Map;
import java.util.ServiceLoader;
import java.util.Set;

import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

public class TheoremProverFactory {
  /** Theorem prover capabilities, i.e., optional features that a theorem prover
      supports. */
  public static enum Capability {
    /** Satisfiability modulo theories (general first-order solving) */
    SMT, 

    /** BDD representation */
    BDD, 

   /** Datatype theories */
   DATATYPES
  }
  
  public static final String DEFAULT_PLUGINS_DIRECTORY_NAME = "plugins";
  public static final File DEFAULT_PLUGINS_DIRECTORY = 
    new File(Preferences.DEFAULT_CONFIG_DIRECTORY, DEFAULT_PLUGINS_DIRECTORY_NAME);

  private static final String OPTION_PROVER = "prover";

  /** Has <code>discover()</code> been called yet? */
  private static boolean discoverCalled = false;

  @SuppressWarnings("serial")
  public static class TheoremProverFactoryException extends Exception {
    TheoremProverFactoryException(String msg) {
      super(msg);
    }
  }
  
  private static final Set<TheoremProver.Provider> allProviders = Sets.newHashSet();
  private static final Map<Capability, ImmutableSet<TheoremProver.Provider>> capMap = Maps.newEnumMap(Capability.class);
  private static final Map<String, TheoremProver.Provider> nameMap = Maps.newHashMap();

  /** Searches through the classpath and the plugins directory for providers
      of {@link TheoremProver} instances.

      @see java.util.ServiceLoader 
  */
  public static void discover() {
    discoverCalled = true;

    /* Give preference to the user-supplied plugins dir */
    File pluginsDir = Preferences.getFile(Preferences.OPTION_PLUGINS_DIRECTORY);

    if (pluginsDir != null && !pluginsDir.canRead()) {
      IOUtils.err().println("Can't read plugins directory: " + pluginsDir);
      pluginsDir = null;
    }

    /* If no user-supplied dir, use default */
    if (pluginsDir == null) {
      pluginsDir = DEFAULT_PLUGINS_DIRECTORY;
      if( !pluginsDir.canRead() ) {
        IOUtils.err().println("Can't read plugins directory: " + pluginsDir);
        pluginsDir = null;
      }
    }

    ClassLoader classLoader = ClassLoader.getSystemClassLoader();

    if( pluginsDir != null ) {
      IOUtils.debug().pln("Plugins dir: " + pluginsDir);
    
      /* Get a list of the JARs in the plugins dir */
      File[] jarFiles = pluginsDir.listFiles(new FileFilter() {
          @Override
          public boolean accept(File pathname) {
            return pathname.getName().endsWith(".jar");
          }
        });

      /* Convert JAR names to URLs */
      URL[] jarUrls = new URL[jarFiles.length];
      for (int i = 0; i < jarFiles.length; i++) {
        IOUtils.debug().pln("Plugin JAR: " + jarFiles[i]);
        try {
          jarUrls[i] = jarFiles[i].toURI().toURL();
        } catch (MalformedURLException e) {
          e.printStackTrace(IOUtils.err());
          assert false;
        }
      }
    
      /* Inspect the JARs for TheoremProver providers */
      classLoader = new URLClassLoader(jarUrls, classLoader);
    }

    ServiceLoader<TheoremProver.Provider> tpServiceLoader = ServiceLoader.load(
        TheoremProver.Provider.class, classLoader);

    if( Iterables.isEmpty(tpServiceLoader) ) {
      IOUtils.err().println("No theorem prover providers found.");
      IOUtils.err().println("Put plugin JAR in CLASSPATH or " 
                            + DEFAULT_PLUGINS_DIRECTORY.getAbsolutePath());
    }
    
    /* Register each TheoremProver provider */ 
    for (TheoremProver.Provider tp : tpServiceLoader) {
      IOUtils.debug().pln("Theorem prover: " + tp.getName());
      register(tp);
    }
  }

  /** Register a <code>TheoremProver</code> instance with the factory. */
  public static void register(TheoremProver.Provider tp) {
    // Register as an instance
    allProviders.add(tp);
    // Map name to instance
    nameMap.put(tp.getName(),tp);
    // Map capabilities to instance
    for (Capability cap : tp.getCapabilities()) {
      IOUtils.debug().pln("Capability: " + cap);
      ImmutableSet<TheoremProver.Provider> s = getProvidersWithCapability(cap);
      s = ImmutableSet.<TheoremProver.Provider>builder().addAll(s).add(tp).build();
      capMap.put(cap, s);
    }
  }
  
  /** Get a <code>TheoremProver</code> instance. If the <code>OPTION_PROVER</code>
      preference is set, then an instance matching that preference will be returned.
      Otherwise, an arbitrary instance will be chosen.

      This method will invoke <code>discover()</code> if it has not previously 
      been called.

      @throws TheoremProverFactoryException if no instances are registered, or if
      an instance satisfying the <code>OPTION_PROVER</code> preference is not 
      available.
  */
  public static TheoremProver getInstance()
      throws TheoremProverFactoryException {
    TheoremProver.Provider tp;
    if( !discoverCalled ) {
      discover();
    }

    if (Preferences.isSet(OPTION_PROVER)) {
      String name = Preferences.getString(OPTION_PROVER);
      tp = nameMap.get(name);
      if (tp == null) {
        throw new TheoremProverFactoryException(
            "No registered theorem prover with name: '" + name + "'");
      }
    } else {
      tp = chooseProvider(allProviders);
      if (tp == null) {
        throw new TheoremProverFactoryException(
            "No theorem prover instances registered.");
      }
    }
    return tp.create();
  }

  /** Get a list of options associated with the factory and all of its
      registered <code>TheoremProver</code> instances.

      This method will invoke <code>discover()</code> if it has not previously 
      been called.
  */

  @SuppressWarnings("static-access")
  public static ImmutableList<Option> getOptions() {
    if( !discoverCalled ) {
      discover();
    }

    ImmutableList.Builder<Option> listBuilder = ImmutableList.builder();
    listBuilder.add(OptionBuilder.withLongOpt(OPTION_PROVER) //
        .hasArg() //
        .withArgName("NAME") //
        .withDescription("Enable the named theorem prover plugin") //
        .create());
    for (TheoremProver.Provider tp : allProviders) {
      /*
       * listBuilder.add(OptionBuilder.withLongOpt(tp.getName()) //
       * .withDescription( "Enable the " + tp.getName() +
       * " theorem prover plugin") // .create());
       */
      listBuilder.addAll(tp.getOptions());
    }
    return listBuilder.build();
  }
  
  
  /** Get an SMT-capable <code>TheoremProver</code> instance If
      multiple SMT-capable instances are available, an arbitrary
      instance will be chosen.

      This method will invoke <code>discover()</code> if it has not previously 
      been called.

      @throws TheoremProverFactoryException if no SMT-capable instances are 
      available.
  */

  public static TheoremProver getSmtInstance() throws TheoremProverFactoryException {
    if( !discoverCalled ) {
      discover();
    }

    return getInstance(Capability.SMT);
  }


  /** Get a <code>TheoremProver</code> instance with all of the given capabilities. 
      If multiple instances have the given capabilities, an arbitrary
      instance will be chosen.

      This method will invoke <code>discover()</code> if it has not previously 
      been called.

      @throws TheoremProverFactoryException if no instances with all of the given
      capabilities are available.
  */

  public static TheoremProver getInstance(Capability... capabilities) 
    throws TheoremProverFactoryException {
    if( !discoverCalled ) {
      discover();
    }

    Set<TheoremProver.Provider> candidates = allProviders;
    for( Capability cap : capabilities ) {
      Set<TheoremProver.Provider> s = getProvidersWithCapability(cap);
      candidates = Sets.intersection(candidates, s);
    }
    TheoremProver.Provider tp = chooseProvider(candidates);
    if( tp == null ) {
      throw new TheoremProverFactoryException("Unsatisfiable capabilities: " + capabilities);
    } else {
      return tp.create();
    }
  }

  /** Choose an arbitrary <code>TheoremProver</code> instance from the set. */
  private static TheoremProver.Provider chooseProvider(Set<TheoremProver.Provider> candidates) {
    if( candidates.isEmpty() ) {
      return null;
    } else {
      return Iterables.get(candidates,0);
    }
  }

  /** Return a set of all the registered <code>TheoremProver</code> instances with
      the given capability. */
  private static ImmutableSet<TheoremProver.Provider> getProvidersWithCapability(Capability cap) {
    ImmutableSet<TheoremProver.Provider> s = capMap.get(cap);
    return s==null ? ImmutableSet.<TheoremProver.Provider>of() : s;
  }
}

