package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.nparser.KeyAst;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;

public class Event extends AbstractSortedOperator {
    public static final Operator instance = new Event(new Name("eventold"));

    private Event(Name name) {
        super(name, new Sort[] { JavaDLTheory.ANY, JavaDLTheory.ANY, JavaDLTheory.ANY}, JavaDLTheory.ANY,
                new Boolean[] { true }, false);
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