package org.key_project.key4eclipse.common.ui.wizard;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.wizards.JavaProjectWizard;
import org.eclipse.jdt.internal.ui.wizards.NewWizardMessages;
import org.key_project.key4eclipse.common.ui.util.LogUtil;

/**
 * Provides a basic functionality for new wizards that are based on 
 * Java Projects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractNewJavaProjectWizard extends JavaProjectWizard {
   /**
    * Constructor.
    */
   public AbstractNewJavaProjectWizard() {
      setWindowTitle(NewWizardMessages.JavaProjectWizard_title + " with content from " + getExampleName());
   }
   
   /**
    * Returns the example name.
    * @return The name of the example.
    */
   protected abstract String getExampleName();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         // Create java project
         boolean done = super.performFinish();
         // Check if the project was created
         if (done) {
            // Get source code directory
            IResource sourceDirectory = getSourceDirectory();
            // Check if a source code directory was found
            if (sourceDirectory instanceof IContainer) {
               done = createExampleContent((IContainer)sourceDirectory);
            }
         }
         return done;
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }

   /**
    * Adds the example content to the given source directory.
    * @param sourceDirectory The given source directory.
    * @return {@code true} = close wizard, {@code false} = keep wizard opened.
    * @throws Exception Occurred Exception.
    */
   protected abstract boolean createExampleContent(IContainer sourceDirectory) throws Exception;

   /**
    * Returns the {@link IResource} that will contain java source code.
    * @return The found {@link IResource} with java source code or {@code null} if no one was found. 
    * @throws JavaModelException Occurred Exception.
    */
   protected IResource getSourceDirectory() throws JavaModelException {
      IResource sourceDirectory = null;
      IJavaElement newElement = getCreatedElement();
      if (newElement != null) {
         IPackageFragmentRoot[] roots = newElement.getJavaProject().getPackageFragmentRoots();
         int i = 0;
         while (sourceDirectory == null && i < roots.length) {
            if (roots[i].getResource() != null) {
               sourceDirectory = roots[i].getResource();
            }
         }
      }
      return sourceDirectory;
   }
}