package edu.nyu.cascade.prover;

import org.junit.Test;

public class TheoremProverFactoryTest {
  @Test
  public void testDiscover() {
    // Shouldn't have an assertion failure!
    // IOUtils.enableDebug();
    TheoremProverFactory.discover();
  }

  //  @Test
  // public void testDiscover2() throws IOException {
    // Shouldn't have an assertion failure!
    // if( TheoremProverFactory.DEFAULT_PLUGINS_DIRECTORY.canRead() ) {
    //   TheoremProverFactory.DEFAULT_PLUGINS_DIRECTORY.setReadable(false);

    // System.setSecurityManager( new SecurityManager() {
    //     private final FilePermission pluginsPerm = 
    //       new FilePermission(
    //          TheoremProverFactory.DEFAULT_PLUGINS_DIRECTORY.getCanonicalPath(), 
    //          "read" );

    //     @Override
    //     public void checkPermission(Permission p) {
    //       if( p.implies(pluginsPerm) ) {
    //         throw new SecurityException();
    //       }
    //     }
    //   }
      // );
  //   }
  //   IOUtils.enableDebug();
  //   TheoremProverFactory.discover();
  // }

}
