package org.key_project.jmlediting.ui;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.key_project.jmlediting.ui.util.JMLEditingImages;
import org.key_project.util.eclipse.Logger;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

   // The plug-in ID
   public static final String PLUGIN_ID = "org.key_project.jmlediting.ui"; //$NON-NLS-1$
   public static final String EDITOR_EXTENSION_ID = "org.key_project.jmlediting.ui.extension.JMLSourceViewerConfigurationExtension";

   // The shared instance
   private static Activator plugin;

   /**
    * The constructor
    */
   public Activator() {
   }

   public static Logger createLogger() {
      return new Logger(Activator.getDefault(), Activator.PLUGIN_ID);
   }

   /*
    * (non-Javadoc)
    *
    * @see
    * org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext
    * )
    */
   @Override
   public void start(final BundleContext context) throws Exception {
      super.start(context);
      plugin = this;
   }

   /*
    * (non-Javadoc)
    *
    * @see
    * org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext
    * )
    */
   @Override
   public void stop(final BundleContext context) throws Exception {
      JMLEditingImages.disposeImages();
      plugin = null;
      super.stop(context);
   }

   /**
    * Returns the shared instance
    *
    * @return the shared instance
    */
   public static Activator getDefault() {
      return plugin;
   }

}