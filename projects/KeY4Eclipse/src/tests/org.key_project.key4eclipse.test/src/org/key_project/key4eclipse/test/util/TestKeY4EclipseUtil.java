package org.key_project.key4eclipse.test.util;

import org.key_project.util.java.StringUtil;

/**
 * Provides static methods that makes testing easier.
 * @author Martin Hentschel
 */
public final class TestKeY4EclipseUtil {
   /**
    * Forbid instances.
    */
   private TestKeY4EclipseUtil() {
   }
   
   /**
    * Creates an operation contract ID.
    * @param qualifiedName The qualified class name.
    * @param method The method signature.
    * @param id The unique ID.
    * @param behavior The behavior.
    * @return The created operation contract ID:
    */
   public static String createOperationContractId(String qualifiedName,
                                                  String method,
                                                  String id,
                                                  String behavior) {
      return qualifiedName + "[" + qualifiedName + "::" + method + "].JML " + (StringUtil.isEmpty(behavior) ? "" : behavior + " ") + "operation contract." + id + "";
   }

   /**
    * Creates the ID for an axiom contract.
    * @param qualifiedName The full qualified class name.
    * @param field The field.
    * @param id The unique ID.
    * @return the create axiom contract ID.
    */
   public static String createAxiomContractId(String qualifiedName, String field, String id) {
      return qualifiedName + "[" + qualifiedName + "::" + field+ "].JML accessible clause." + id;
   }
}