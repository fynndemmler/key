package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IReason;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.context.impl.LayoutContext;
import org.eclipse.graphiti.features.impl.AbstractUpdateFeature;
import org.eclipse.graphiti.features.impl.Reason;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Provides a basic implementation of {@link IUpdateFeature} for {@link ISEDDebugNode}s.
 * </p>
 * </p>
 * A subtree is constructed as follows during execution of {@link #update(IUpdateContext)}
 * 
 * <ol>
 *    <li>Update label of current node via {@link #updateName(PictogramElement, IProgressMonitor)} </li>
 *    <li>
 *       Update sub tree via {@link #updateChildren(PictogramElement, IProgressMonitor)}
 *       <ol>
 *          <li>
 *             Add missing graphical representations in a tree where each branch is left centered.
 *             Result is a list of leaf nodes computed via {@link #updateChildrenLeftAligned(ISEDDebugElement, IProgressMonitor, int)}
 *             <ol>
 *                <li>Iterate over subtree in order.</li>
 *                <li>First branch (ends in first leaf node) is completely left centered with x = 0.</li>
 *                <li>
 *                   If a new branch is detected, the maximal width of the previous 
 *                   child branch is computed via {@link #computeSubTreeBounds(ISEDDebugNode)}
 *                   and the x coordinate is the maximal bound (x + width) + a given offset of two grid units.
 *                </li>
 *             </ol>
 *          </li>
 *          <li>
 *             Center whole sub tree starting from its branches leaf nodes via {@link #centerChildren(Set, IProgressMonitor)}.
 *             <ol>
 *                <li>Iterate over all given leaf nodes. (Start with the found one via {@link #updateChildrenLeftAligned(ISEDDebugElement, IProgressMonitor, int)})</li>
 *                <li>
 *                   If leaf node has children (added during step 4) compute x offset to center branch under his children.
 *                </li>
 *                <li>
 *                   Go back to parents until root is reached (parent is {@code null} or multiple children are detected.
 *                   During backward iteration collect maximal width of the elements.
 *                </li>
 *                <li>
 *                   If the iteration stopped because the parent has multiple children,
 *                   at the parent to leaf node to layout it later on same way. 
 *                </li>
 *                <li>
 *                   Go back to starting child (leaf node) and center each element with the computed maximal width.
 *                </li>
 *             </ol>
 *          </li>
 *       </ol>
 *    </li>
 * </ol>
 * <p>
 * @author Martin Hentschel
 */
public abstract class AbstractDebugNodeUpdateFeature extends AbstractUpdateFeature {
   /**
    * The maximal x coordinate which is used by the previous
    * {@link ISEDDebugTarget} in {@link #updateChildren(PictogramElement, IProgressMonitor)}.
    */
   private int maxX;
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IUpdateFeature}.
    */   
   public AbstractDebugNodeUpdateFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canUpdate(IUpdateContext context) {
      Object bo = getBusinessObjectForPictogramElement(context.getPictogramElement());
      return canUpdateBusinessObject(bo);
   }
   
   /**
    * Checks if the give business object can be handled by this {@link IUpdateFeature}.
    * @param businessObject The business object to check.
    * @return {@code true} can update, {@code false} can not update.
    */
   protected abstract boolean canUpdateBusinessObject(Object businessObject);

   /**
    * {@inheritDoc}
    */
   @Override
   public IReason updateNeeded(IUpdateContext context) {
      try {
         PictogramElement pictogramElement = context.getPictogramElement();
         if (isNameUpdateNeeded(pictogramElement)) {
            return Reason.createTrueReason("Name is out of date.");
         }
         else {
            if (isChildrenUpdateNeeded(pictogramElement)) {
               return Reason.createTrueReason("New children available.");
            }
            else {
               return Reason.createFalseReason();
            }
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return Reason.createFalseReason(e.getMessage());
      }
   }
   
   /**
    * Checks if the shown name in the given {@link PictogramElement}
    * is equal to the name defined by his business object 
    * ({@link ISEDDebugNode#getName()}).
    * @param pictogramElement The {@link PictogramElement} to check.
    * @return {@code true} name is different and an update is required, {@code false} name is the same and no update is required.
    * @throws DebugException Occurred Exception.
    */
   protected boolean isNameUpdateNeeded(PictogramElement pictogramElement) throws DebugException {
      String pictogramName = getPictogramName(pictogramElement);
      String businessName = getBusinessName(pictogramElement);
      return !ObjectUtil.equals(businessName, pictogramName);  
   }
   
   /**
    * Checks if all child {@link ISEDDebugNode} of the {@link ISEDDebugNode}
    * which is the business object of the given {@link PictogramElement} have
    * a graphical representation. 
    * @param pictogramElement The {@link PictogramElement} to check.
    * @return {@code false} all children have graphical representation, {@code true} at least one child has no graphical representation.
    * @throws DebugException Occurred Exception
    */
   protected boolean isChildrenUpdateNeeded(PictogramElement pictogramElement) throws DebugException {
      return !haveAllBusinessObjectChildrenHaveGraphicalRepresentation(pictogramElement);
   }
   
   /**
    * Checks if all child {@link ISEDDebugNode} of the {@link ISEDDebugNode}
    * which is the business object of the given {@link PictogramElement} have
    * a graphical representation. 
    * @param pictogramElement The {@link PictogramElement} to check.
    * @return {@code true} all children have graphical representation, {@code false} at least one child has no graphical representation.
    * @throws DebugException Occurred Exception
    */
   protected boolean haveAllBusinessObjectChildrenHaveGraphicalRepresentation(PictogramElement pictogramElement) throws DebugException {
      Object bo = getBusinessObjectForPictogramElement(pictogramElement);
      boolean childrenHavePictogramElement = true;
      if (bo instanceof ISEDDebugNode) {
         ISEDDebugNode[] children = ((ISEDDebugNode)bo).getChildren();
         int i = 0;
         while (childrenHavePictogramElement && i < children.length) {
            PictogramElement childPE = getPictogramElementForBusinessObject(children[i]);
            childrenHavePictogramElement = childPE != null;
            i++;
         }
      }
      return childrenHavePictogramElement;
   }

   /**
    * This method is similar to the method {@link IFeatureProvider#getAllPictogramElementsForBusinessObject(Object)}, 
    * but only return the first PictogramElement.
    * @param businessObject the business object
    * @return linked pictogram element.
    */
   protected PictogramElement getPictogramElementForBusinessObject(Object businessObject) {
      return getFeatureProvider().getPictogramElementForBusinessObject(businessObject);
   }
   
   /**
    * Returns the name defined in the {@link PictogramElement}.
    * @param pictogramElement The {@link PictogramElement} for that the shown name is needed.
    * @return The name in the {@link PictogramElement}.
    */
   protected String getPictogramName(PictogramElement pictogramElement) {
      Text text = findNameText(pictogramElement);
      if (text != null) {
         return text.getValue();
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the name defined by the business object of the given {@link PictogramElement}
    * which is {@link ISEDDebugNode#getName()}.
    * @param pictogramElement The {@link PictogramElement} for that the business name is needed.
    * @return The name defined by the business object of the given {@link PictogramElement}.
    * @throws DebugException The business name.
    */
   protected String getBusinessName(PictogramElement pictogramElement) throws DebugException {
      Object bo = getBusinessObjectForPictogramElement(pictogramElement);
      if (bo instanceof ISEDDebugNode) {
         return ((ISEDDebugNode)bo).getName();
      }
      else {
         return null;
      }
   }
   
   /**
    * Finds the {@link Text} which shows the name ({@link ISEDDebugNode#getName()}).
    * @param pictogramElement The {@link PictogramElement} to search the {@link Text} in.
    * @return The found {@link Text} or {@code null} if no one was found.
    */
   protected Text findNameText(PictogramElement pictogramElement) {
      Text result = null;
      if (pictogramElement.getGraphicsAlgorithm() instanceof Text) {
         result = (Text)pictogramElement.getGraphicsAlgorithm();
      }
      else if (pictogramElement instanceof ContainerShape) {
         ContainerShape cs = (ContainerShape)pictogramElement;
         for (Shape shape : cs.getChildren()) {
            result = findNameText(shape);
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean update(IUpdateContext context) {
      try {
         // Define monitor to use
         IProgressMonitor monitor;
         Object contextMonitor = context.getProperty(ExecutionTreeUtil.CONTEXT_PROPERTY_MONITOR);
         if (contextMonitor instanceof IProgressMonitor) {
            monitor = (IProgressMonitor)contextMonitor;
         }
         else {
            monitor = new NullProgressMonitor();
         }
         // Retrieve name from business model
         PictogramElement pictogramElement = context.getPictogramElement();
         monitor.beginTask("Update element: " + pictogramElement, 2);
         boolean success = updateName(pictogramElement, new SubProgressMonitor(monitor, 1));
         monitor.worked(1);
         if (success) {
            success = updateChildren(pictogramElement, new SubProgressMonitor(monitor, 1));
         }
         monitor.worked(2);
         monitor.done();
         return success;
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }

   /**
    * Updates the shown name in the given {@link PictogramElement}.
    * @param pictogramElement The {@link PictogramElement} to update.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return {@code true}, if update process was successful
    * @throws DebugException Occurred Exception.
    */
   protected boolean updateName(PictogramElement pictogramElement, 
                                IProgressMonitor monitor) throws DebugException {
      try {
         if (!monitor.isCanceled()) {
            // Set name in pictogram model
            monitor.beginTask("Update labels", 1);
            Text text = findNameText(pictogramElement);
            if (text != null) {
               // Change value
               String businessName = getBusinessName(pictogramElement);
               text.setValue(businessName);
               // Optimize layout
               LayoutContext layoutContext = new LayoutContext(pictogramElement);
               layoutContext.putProperty(AbstractDebugNodeLayoutFeature.WIDTH_TO_SET, AbstractDebugNodeAddFeature.computeInitialWidth(getDiagram(), businessName, text.getFont()));
               layoutContext.putProperty(AbstractDebugNodeLayoutFeature.HEIGHT_TO_SET, AbstractDebugNodeAddFeature.computeInitialHeight(getDiagram(), businessName, text.getFont()));
               getFeatureProvider().layoutIfPossible(layoutContext);
               // Add children
               return true;
            }
            else {
               return false;
            }
         }
         else {
            return false;
         }
      }
      finally {
         monitor.worked(1);
         monitor.done();
      }
   }
   
   /**
    * Updates the children of the {@link ISEDDebugNode} represented
    * by the given {@link PictogramElement}.
    * @param pictogramElement The {@link PictogramElement} to update.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return {@code true}, if update process was successful
    * @throws DebugException Occurred Exception.
    */
   protected boolean updateChildren(PictogramElement pictogramElement, 
                                    IProgressMonitor monitor) throws DebugException {
      monitor.beginTask("Update children", IProgressMonitor.UNKNOWN);
      final int OFFSET = getDiagram().getGridUnit() * 2;
      maxX = 0;
      try {
         if (!monitor.isCanceled()) {
            Object[] bos = getAllBusinessObjectsForPictogramElement(pictogramElement);
            int i = 0;
            while (i < bos.length && !monitor.isCanceled()) {
               if (bos[i] instanceof ISEDDebugElement) {
                  // Add all children left aligned
                  Set<ISEDDebugNode> leafs = updateChildrenLeftAligned((ISEDDebugElement)bos[i], monitor, OFFSET, maxX + OFFSET);
                  monitor.worked(1);
                  // Center sub tree
                  centerChildren(leafs, monitor);
                  monitor.worked(1);
               }
               i++;
            }
         }
         return true;
      }
      finally {
         monitor.done();
      }
   }

   /**
    * Creates for each element starting at the given business object
    * a graphical representation and forms a left aligned tree.
    * @param businessObject The business object to create graphical representations for.
    * @param monitor The {@link IProgressMonitor} to use.
    * @param offsetBetweenPictogramElements The offset between {@link PictogramElement}s.
    * @param initialX The initial X value which is used if no parentPE is defined.
    * @return The found leaf {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected Set<ISEDDebugNode> updateChildrenLeftAligned(ISEDDebugElement businessObject, 
                                                          IProgressMonitor monitor, 
                                                          int offsetBetweenPictogramElements,
                                                          int initialX) throws DebugException {
      Set<ISEDDebugNode> leafs = new LinkedHashSet<ISEDDebugNode>();
      ISEDIterator iter = new SEDPreorderIterator(businessObject);
      PictogramElement parentPE = null;
      while (iter.hasNext() && !monitor.isCanceled()) {
         ISEDDebugElement next = iter.next();
         PictogramElement nextPE = getPictogramElementForBusinessObject(next);
         if (nextPE == null) {
            if (next instanceof ISEDDebugNode) { // Ignore ISEDDebugTarget which has no graphical representation
               ISEDDebugNode nextNode = (ISEDDebugNode)next;
               createGraphicalRepresentationForSubtree(parentPE, nextNode, offsetBetweenPictogramElements, initialX);
               nextPE = getPictogramElementForBusinessObject(next);
               if (nextPE != null) {
                  // Update maxX to make sure that ISEDDebugTargets don't overlap each other.
                  GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
                  if (nextGA.getX() + nextGA.getWidth() > maxX) {
                     maxX = nextGA.getX() + nextGA.getWidth();
                  }
               }
               if (ArrayUtil.isEmpty(nextNode.getChildren())) {
                  leafs.add(nextNode);
               }
            }
         }
         parentPE = nextPE;
         monitor.worked(1);
      }
      return leafs;
   }
   
   /**
    * Creates a new graphical representation for the given {@link ISEDDebugNode}.
    * @param parentPE The {@link PictogramElement} of {@link ISEDDebugNode#getParent()} or {@code null} if it is an {@link ISEDThread}.
    * @param root The {@link ISEDDebugNode} for that a graphical representation is needed.
    * @param offsetBetweenPictogramElements The offset between {@link PictogramElement}s, e.g. to parent or to previous sibling.
    * @param initialX The initial X value which is used if no parentPE is defined.
    * @throws DebugException Occurred Exception.
    */
   protected void createGraphicalRepresentationForSubtree(PictogramElement parentPE,
                                                          ISEDDebugNode root,
                                                          int offsetBetweenPictogramElements,
                                                          int initialX) throws DebugException {
      AreaContext areaContext = new AreaContext();
      if (parentPE != null) {
         ISEDDebugNode parent = root.getParent();
         if (parent != null) {
            ISEDDebugNode previousSibling = ArrayUtil.getPrevious(parent.getChildren(), root);
            if (previousSibling != null) {
               // Compute bounds of the sub tree starting by the previous sibling.
               Rectangle previousBounds = computeSubTreeBounds(previousSibling);
               if (previousBounds != null) {
                  // Add right to the previous sibling directly under parent
                  areaContext.setX(previousBounds.width() + offsetBetweenPictogramElements); 
                  areaContext.setY(previousBounds.y());
               }
               else {
                  // Add directly under parent
                  GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();
                  areaContext.setX(parentGA.getX()); 
                  areaContext.setY(parentGA.getY() + parentGA.getHeight() + offsetBetweenPictogramElements);
               }
            }
            else {
               // Add directly under parent
               GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();
               areaContext.setX(parentGA.getX()); 
               areaContext.setY(parentGA.getY() + parentGA.getHeight() + offsetBetweenPictogramElements);
            }
         }
         else {
            // Add directly under parent
            GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();
            areaContext.setX(parentGA.getX()); 
            areaContext.setY(parentGA.getY() + parentGA.getHeight() + offsetBetweenPictogramElements);
         }
      }
      else {
         areaContext.setLocation(initialX, getDiagram().getGridUnit());
      }
      AddContext addContext = new AddContext(areaContext, root);
      addContext.setTargetContainer(getDiagram());

      // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
      IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
      if (feature != null && feature.canExecute(addContext)) {
         feature.execute(addContext);
      }
   }

   /**
    * Computes the bounds of the sub tree starting at the given {@link ISEDDebugNode}.
    * @param root The sub tree.
    * @return The bounds of the subtree where {@link Rectangle#x()}, {@link Rectangle#y()} is the minimal point and {@link Rectangle#width()}, {@link Rectangle#height()} the maximal point. The result is {@code null} if the subtree is {@code null} or has no graphical representations.
    * @throws DebugException Occurred Exception.
    */
   protected Rectangle computeSubTreeBounds(ISEDDebugNode root) throws DebugException {
      Rectangle result = null;
      if (root != null) {
         ISEDIterator iter = new SEDPreorderIterator(root);
         while (iter.hasNext()) {
            ISEDDebugElement next = iter.next();
            PictogramElement nextPE = getPictogramElementForBusinessObject(next);
            if (nextPE != null) {
               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
               if (result == null) {
                  result = new Rectangle(nextGA.getX(), nextGA.getY(), nextGA.getWidth(), nextGA.getHeight());
               }
               else {
                  if (nextGA.getX() < result.x()) {
                     result.setX(nextGA.getX());
                  }
                  if (nextGA.getY() < result.y()) {
                     result.setY(nextGA.getY());
                  }
                  if (nextGA.getX() + nextGA.getWidth() > result.width()) {
                     result.setWidth(nextGA.getX() + nextGA.getWidth());
                  }
                  if (nextGA.getY() + nextGA.getHeight() > result.height()) {
                     result.setHeight(nextGA.getY() + nextGA.getHeight());
                  }
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Centers all nodes starting from the given leaf nodes.
    * @param leafs All leaf nodes.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void centerChildren(Set<ISEDDebugNode> leafs, 
                                 IProgressMonitor monitor) throws DebugException {
      while (!leafs.isEmpty() && !monitor.isCanceled()) {
         // Get leaf to center
         ISEDDebugNode next = CollectionUtil.removeFirst(leafs);
         PictogramElement nextPE = getPictogramElementForBusinessObject(next);
         // Compute new x margin to center current branch under his children 
         int xMargin;
         int xStart;
         if (!ArrayUtil.isEmpty(next.getChildren())) {
            ISEDDebugNode firstChild = ArrayUtil.getFirst(next.getChildren());
            ISEDDebugNode lastChild = ArrayUtil.getLast(next.getChildren());
            PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
            PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
            int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
                             firstChildPE.getGraphicsAlgorithm().getX(); 
            xMargin = (childWidth - nextPE.getGraphicsAlgorithm().getWidth()) / 2;
            xStart = firstChildPE.getGraphicsAlgorithm().getX();
         }
         else {
            xMargin = 0;
            xStart = nextPE.getGraphicsAlgorithm().getX();
         }
         // Go back to root or branch split and collect descendants while computing max width
         // If a parent node has more than one child it is treated as leaf node in a further iteration by adding it to leafs
         List<PictogramElement> descendantsPE = new LinkedList<PictogramElement>();
         int maxWidth = 0;
         boolean maxInitialised = false;
         do {
            nextPE = getPictogramElementForBusinessObject(next);
            descendantsPE.add(nextPE);
            int currentWidth = nextPE.getGraphicsAlgorithm().getWidth();
            if (maxInitialised) {
               if (currentWidth > maxWidth) {
                  maxWidth = currentWidth;
               }
            }
            else {
               maxWidth = currentWidth;
               maxInitialised = true;
            }
            ISEDDebugNode child = next;
            next = child.getParent();
            if (next != null && next.getChildren().length != 1) {
               if (ArrayUtil.isLast(next.getChildren(), child)) {  // Update parent only if all of his branches are correctly centered
                  leafs.add(next);
               }
               next = null;
            }
         } while (next != null && !monitor.isCanceled());
         // Center collected descendants based on the computed maximal element width
         Iterator<PictogramElement> descendantIter = descendantsPE.iterator();
         while (descendantIter.hasNext() && !monitor.isCanceled()) {
            PictogramElement pe = descendantIter.next();
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            ga.setX(xMargin + xStart + (maxWidth - ga.getWidth()) / 2);
         }
         monitor.worked(1);
      }
   }
}