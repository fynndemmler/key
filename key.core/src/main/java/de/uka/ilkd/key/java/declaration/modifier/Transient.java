/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;

import org.key_project.util.ExtList;

/**
 * Transient.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Transient extends Modifier {

    /**
     * Transient.
     */

    public Transient() {}

    /**
     * Transient.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */

    public Transient(ExtList children) {
        super(children);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "transient";
    }
}
