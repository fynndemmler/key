package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.McUpdate;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;

public class IsParallelUpdateCondition extends VariableConditionAdapter {
    private SchemaVariable update;
    private boolean negated;

    public IsParallelUpdateCondition(SchemaVariable update, boolean negated) {
        this.update = update;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap, Services services) {
        Term potentialMcUpdate = (Term) instMap.getInstantiation(this.update);
        var ret = potentialMcUpdate.op() == de.uka.ilkd.key.logic.op.UpdateJunctor.PARALLEL_UPDATE;
        return ret != negated;
    }
}