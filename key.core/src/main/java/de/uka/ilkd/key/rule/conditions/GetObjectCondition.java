package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;

/**
 * Converts a {@link ReferencePrefix} into its corresponding {@link Term} and instantiates the schema variable {@code
 * objPlaceholder} with it.
 */
public class GetObjectCondition implements VariableCondition {
    private final SchemaVariable objPlaceholder;
    private final SchemaVariable objName;

    public GetObjectCondition(SchemaVariable objPlaceholder, SchemaVariable objName) {
        this.objPlaceholder = objPlaceholder;
        this.objName = objName;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
                                 MatchConditions mc,
                                 Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        var ec = svInst.getContextInstantiation().activeStatementContext();
        ReferencePrefix rp = (ReferencePrefix) svInst.getInstantiation(this.objName);
        if (rp == null || ec == null) {
            return mc;
        }
        Term logicElem = null;
        if (rp == null || rp instanceof ThisReference || rp instanceof SuperReference) {
            var newRp = ((FieldReference) rp).setReferencePrefix(ec.getRuntimeInstance());
            logicElem = services.getTypeConverter().convertToLogicElement(newRp);
        } else {
            logicElem = services.getTypeConverter().convertToLogicElement(rp, ec);
        }
        var ret = svInst.add(this.objPlaceholder, logicElem, services);
        return mc.setInstantiations(ret);
    }
}
