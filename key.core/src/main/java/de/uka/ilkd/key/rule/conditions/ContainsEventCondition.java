package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SortCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Event;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;

/**
 * Returns {@code !negated} iff a given {@link Term} contains an {@link Event}, else {@code negated}.
 */
public class ContainsEventCondition extends VariableConditionAdapter {
    private final SchemaVariable formula;
    private final boolean negated;

    public ContainsEventCondition(SchemaVariable formula, boolean negated) {
        this.formula = formula;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap, Services services) {
        var formulaInst = instMap.getInstantiation(this.formula);
        if (!(formulaInst instanceof Term formulaT)) {
            return false;
        }
        SortCollector collector = new SortCollector();
        formulaT.execPostOrder(collector);
        for (var op : collector.getSorts()) {
            if (op.name().toString().equals("Event")) {
                return !negated;
            }
        }
        return negated;
    }
}
