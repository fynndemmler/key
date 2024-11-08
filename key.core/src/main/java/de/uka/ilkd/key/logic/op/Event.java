package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;

public class Event extends AbstractSortedOperator {
    public static final Name EVENT_NAME = new Name("event");
    public static final Operator instance = new Event(EVENT_NAME);

    private Event(Name name) {
        super(name, new Sort[] { JavaDLTheory.FORMULA }, JavaDLTheory.FORMULA,
                new Boolean[] { true }, true);
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
