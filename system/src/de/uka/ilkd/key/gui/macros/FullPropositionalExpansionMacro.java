// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.macros;

import java.util.Set;

/**
 * The macro FullPropositionalExpansionMacro apply rules to decompose
 * propositional toplevel formulas; it even splits the goal if necessary.
 *
 * The rules that are applied can be set in {@link #ADMITTED_RULES}.
 *
 * @author mattias ulbrich
 */
public class FullPropositionalExpansionMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Propositional expansion (w/ splits)";
    }

    @Override
    public String getDescription() {
        return "Apply rules to decompose propositional toplevel formulas; " +
                "splits the goal if necessary";
    }

    private static final String[] ADMITTED_RULES = {
        "andLeft", "orRight", "impRight", "notLeft", "notRight", "close",
        "andRight", "orLeft", "impLeft"
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

}