package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.SortCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.EventUpdate;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.EventUpdateCollector;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;

public class ContainsEventUpdateCondition extends VariableConditionAdapter {
    private final SchemaVariable update;
    private final boolean negated;

    public ContainsEventUpdateCondition(SchemaVariable update, boolean negated) {
        this.update = update;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap, Services services) {
        var updateInst = instMap.getInstantiation(this.update);
        if (!(updateInst instanceof Term)) {
            return false;
        }
        var collector = new EventUpdateCollector();
        ((Term)updateInst).execPostOrder(collector);
        return negated == collector.result().isEmpty();
    }
}


