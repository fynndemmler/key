package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.EventUpdate;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;

/**
 * Return {@code true} if a given update is an {@link de.uka.ilkd.key.logic.op.EventUpdate}, otherwise {@code false};
 */
public class IsEventUpdateCondition extends VariableConditionAdapter {
    private SchemaVariable update;

    public IsEventUpdateCondition(SchemaVariable update) {
        this.update = update;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap, Services services) {
        Term potentialEventUpdate = (Term) instMap.getInstantiation(this.update);
        var ret = potentialEventUpdate.op() instanceof EventUpdate;
        return ret;
    }
}
