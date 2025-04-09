package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;

public class McUpdate extends AbstractSortedOperator {
    public static final Operator instance = new McUpdate(new Name("mcUpdate"));

    private McUpdate(Name name) {
        super(name, new Sort[]{JavaDLTheory.ANY}, JavaDLTheory.UPDATE, false);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException(name() + " has no children");
    }
}
