package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.McUpdateCollector;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;

public class ContainsMcUpdateCondition extends VariableConditionAdapter {
    private final SchemaVariable update;
    private final boolean negated;

    public ContainsMcUpdateCondition(SchemaVariable update, boolean negated) {
        this.update = update;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap, Services services) {
        var updateInst = instMap.getInstantiation(this.update);
        if (!(updateInst instanceof Term)) {
            return false;
        }
        var collector = new McUpdateCollector();
        ((Term)updateInst).execPostOrder(collector);
        return negated == collector.result().isEmpty();
    }
}


