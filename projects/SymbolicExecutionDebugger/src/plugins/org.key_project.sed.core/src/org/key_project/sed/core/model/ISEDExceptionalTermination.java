package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.impl.AbstractSEDExceptionalTermination;
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalTermination;

/**
 * A node in the symbolic execution tree which represents an exceptional termination of a branch,
 * e.g. {@code throws Exception}.
 * <p>
 * A symbolic exceptional termination is also a normal stack frame ({@link IStackFrame})
 * for compatibility reasons with the Eclipse debug API.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDExceptionalTermination} instead of implementing this
 * interface directly. {@link SEDMemoryExceptionalTermination} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDExceptionalTermination extends ISEDTermination {

}