package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SortCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;

public class DropEffectlessMcUpdatesCondition implements VariableCondition {
    private UpdateSV u;
    private SchemaVariable target;
    private SchemaVariable result;

    public DropEffectlessMcUpdatesCondition(UpdateSV u, SchemaVariable target, SchemaVariable result) {
        this.u = u;
        this.target = target;
        this.result = result;
    }

    private boolean containsMethodId(Term term) {
        SortCollector collector = new SortCollector();
        term.execPostOrder(collector);
        for (var op : collector.getSorts()) {
            if (op.name().toString().equals("MethodId")) {
                return true;
            }
        }
        return false;
    }

    private Term dropEffectlessMcUpdatesRecursively(Term update, Services services) {
        if (update.op() instanceof ElementaryUpdate eu) {
            return update;//services.getTermBuilder().elementary(eu.lhs(), update.sub(0));
        } else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
            Term sub0 = update.sub(0);
            Term sub1 = update.sub(1);
            // first descend to the second sub-update to keep relevantVars in
            // good order
            Term newSub1 = dropEffectlessMcUpdatesRecursively(sub1, services);
            Term newSub0 = dropEffectlessMcUpdatesRecursively(sub0, services);
            if (newSub0 == null && newSub1 == null) {
                return null;
            } else {
                newSub0 = newSub0 == null ? sub0 : newSub0;
                newSub1 = newSub1 == null ? sub1 : newSub1;
                return services.getTermBuilder().parallel(newSub0, newSub1);
            }
        } else if (update.op() == UpdateApplication.UPDATE_APPLICATION) {
            Term sub0 = update.sub(0);
            Term sub1 = update.sub(1);
            Term newSub1 = dropEffectlessMcUpdatesRecursively(sub1, services);
            return newSub1 == null ? null : services.getTermBuilder().apply(sub0, newSub1, null);
        } else if (update.op() == McUpdate.instance) {
            return services.getTermBuilder().skip();
        }
        else {
            return null;
        }
    }

    private Term dropEffectlessMcUpdates(Term uInst, Term targetInst, Services services) {
        Term finalUpdate = dropEffectlessMcUpdatesRecursively(uInst, services);
        return finalUpdate == null ? null : services.getTermBuilder().apply(finalUpdate, targetInst);
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate, MatchConditions matchCond, Services services) {
        SVInstantiations svInst = matchCond.getInstantiations();
        Term uInst = (Term) svInst.getInstantiation(u);
        Term targetInst = (Term) svInst.getInstantiation(target);
        Term resultInst = (Term) svInst.getInstantiation(result);
        if (uInst == null || targetInst == null) {
            return matchCond;
        }
        if (!containsMethodId(uInst) || containsMethodId(targetInst)) {
            return matchCond;
        }
        Term properResultInst = dropEffectlessMcUpdates(uInst, targetInst, services);
        if (properResultInst == null) {
            return matchCond;
        } else if (resultInst == null) {
            svInst = svInst.add(result, properResultInst, services);
            return matchCond.setInstantiations(svInst);
        } else if (resultInst.equals(properResultInst)) {
            return matchCond;
        } else {
            return null;
        }
    }
}