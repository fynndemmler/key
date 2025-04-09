package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.McUpdate;

import java.util.HashSet;
import java.util.LinkedHashSet;

public class McUpdateCollector implements DefaultVisitor {
    private final HashSet<McUpdate> mcUpdates = new LinkedHashSet<>();

    @Override
    public void visit(Term visited) {
        if (visited.op() instanceof McUpdate) {
            mcUpdates.add((McUpdate)visited.op());
        }
    }

    public HashSet<McUpdate> result() {
        return this.mcUpdates;
    }
}
