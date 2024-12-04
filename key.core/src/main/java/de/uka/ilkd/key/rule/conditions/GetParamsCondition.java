package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Converts a sequence of method call parameters into a {@link KeyAst.Seq}. The result is stored inside the schema
 * variable {@code paramsPlaceholder}.
 */
public class GetParamsCondition implements VariableCondition {
    private final SchemaVariable paramsPlaceholder;
    private final SchemaVariable paramsName;

    public GetParamsCondition(SchemaVariable paramsPlaceholder, SchemaVariable paramsName) {
        this.paramsPlaceholder = paramsPlaceholder;
        this.paramsName = paramsName;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
                                 MatchConditions mc,
                                 Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        var ec = svInst.getContextInstantiation().activeStatementContext();
        ImmutableArray<ProgramElement> paramsInst = (ImmutableArray<ProgramElement>) svInst.getInstantiation(this.paramsName);
        if (paramsInst == null || ec == null) {
            return mc;
        }
        ImmutableList<Term> termLst = ImmutableSLList.nil();
        for (ProgramElement pe : paramsInst) {
            termLst = termLst.append(services.getTypeConverter().convertToLogicElement((ProgramElement) paramsInst, ec));
        }
        var logicElem = services.getTermBuilder().seq(termLst);
        var ret = svInst.add(this.paramsPlaceholder, logicElem, services);
        return mc.setInstantiations(ret);
    }
}
