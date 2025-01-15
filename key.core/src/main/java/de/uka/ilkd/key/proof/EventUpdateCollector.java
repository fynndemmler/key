package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.EventUpdate;

import java.util.HashSet;
import java.util.LinkedHashSet;

public class EventUpdateCollector implements DefaultVisitor {
    private final HashSet<EventUpdate> eventUpdates = new LinkedHashSet<>();

    @Override
    public void visit(Term visited) {
        if (visited.op() instanceof EventUpdate) {
            eventUpdates.add((EventUpdate)visited.op());
        }
    }

    public HashSet<EventUpdate> result() {
        return this.eventUpdates;
    }
}
