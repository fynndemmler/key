package java.util;

import java.util.function.Consumer;

public class BoundedLinkedList
    extends AbstractSequentialList
    implements List, Deque, Cloneable, java.io.Serializable {

    public /*@spec_public*/ boolean condAtBoundedLinkedList_add_Object;
    public /*@spec_public*/ boolean condAtBoundedLinkedList_linkLast_Object;

    /*@ invariant
      @     (*!eventSeq(seqConcat(seqSingleton(\if(event(java_util_BoundedLinkedList_add_java_lang_Object, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(java_util_BoundedLinkedList_linkLast_java_lang_Object, TRUE))\then(TRUE)\else(FALSE))))*);
      @*/

transient int size = 0;


//@ private ghost \seq nodeList;
//@ private ghost \bigint nodeIndex;

// condAtBoundedLikedList_add_Object = this.size >= Integer.MAX_VALUE;
// condAtBoundedLinkedList_linkLast_Object = this.size != Integer.MAX_VALUE;
// TODO: Add conditions before

/*@ invariant
  @   nodeList.length == size &&
  @   nodeList.length <= Integer.MAX_VALUE &&
  @   (\forall \bigint i; 0 <= i < nodeList.length;
  @       nodeList[i] instanceof Node) &&
  @   ((nodeList == \seq_empty && first == null && last == null)
  @    || (nodeList != \seq_empty && first != null &&
  @         first.prev == null && last != null &&
  @         last.next == null && first == (Node)nodeList[0] &&
  @         last == (Node)nodeList[nodeList.length-1])) &&
  @   (\forall \bigint i; 0 < i < nodeList.length;
  @       ((Node)nodeList[i]).prev == (Node)nodeList[i-1]) &&
  @   (\forall \bigint i; 0 <= i < nodeList.length-1;
  @       ((Node)nodeList[i]).next == (Node)nodeList[i+1]);
  @*/

/*@ nullable @*/ transient Node first;
/*@ nullable @*/ transient Node last;

/*@
  @ public normal_behavior
  @   ensures nodeList == \seq_empty;
  @*/
public BoundedLinkedList() {}

/*@
  @ public exceptional_behavior
  @   requires
  @     c == null;
  @   signals_only NullPointerException;
  @   signals (NullPointerException e) true;
  @ public exceptional_behavior
  @   requires
  @     c != null && !(0 <= c.size() &&
  @     c.size() <= Integer.MAX_VALUE);
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @ public normal_behavior
  @   requires
  @     c != null && 0 < c.size() &&
  @     c.size() <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \dl_array2seq(c.toArray());
  @ public normal_behavior
  @   requires
  @     c != null && c.size() == 0;
  @   ensures
  @     nodeList == \seq_empty;
  @*/
public BoundedLinkedList(Collection c) {
    this();
    addAll(c);
} // skipped

/*@
  @ private normal_behavior
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\seq_singleton(nodeList[0]),
  @       \old(nodeList)) &&
  @     ((Node)nodeList[0]).item == e;
  @*/
private void linkFirst(/*@ nullable @*/ Object e) {
    final Node f = first;
    final Node newNode = new Node(null, e, f);
    first = newNode;
    if (f == null) last = newNode;
    else f.prev = newNode;
    size++;
    modCount++;
    //@ set nodeList = \seq_concat(\seq_singleton(first),nodeList);
}

/*@
  @ normal_behavior
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\old(nodeList),
  @       \seq_singleton(nodeList[nodeList.length-1])) &&
  @     ((Node)nodeList[nodeList.length-1]).item == e;
  @*/
void linkLast(/*@ nullable @*/ Object e) {
    final Node l = last;
    final Node newNode = new Node(l, e, null);
    last = newNode;
    if (l == null) first = newNode;
    else l.next = newNode;
    size++;
    modCount++;
    //@ set nodeList = \seq_concat(nodeList,\seq_singleton(last));
}

/*@
  @ normal_behavior
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE &&
  @     nodeList != \seq_empty && 
  @     0 <= nodeIndex < nodeList.length &&
  @     (Node)nodeList[nodeIndex] == succ;
  @   ensures
  @     ((Node)nodeList[nodeIndex]).item == e &&
  @     nodeList == \seq_concat(\old(nodeList[0..nodeIndex]),
  @       \seq_concat(\seq_singleton(nodeList[\old(nodeIndex)]),
  @         \old(nodeList[nodeIndex..nodeList.length]))) &&
  @     nodeIndex == \old(nodeIndex);
  @*/
void linkBefore(/*@ nullable @*/ Object e, Node succ)
{
    final Node pred = succ.prev;
    final Node newNode = new Node(pred, e, succ);
    succ.prev = newNode;
    if (pred == null) first = newNode;
    else pred.next = newNode;
    //@ set nodeList = \seq_concat(\dl_seqSub(nodeList,0,nodeIndex), \seq_concat(\dl_seqSingleton(newNode), \dl_seqSub(nodeList,nodeIndex,\dl_seqLen(nodeList))));
    size++;
    modCount++;
}

/*@
  @ private normal_behavior
  @   requires
  @     nodeList != \seq_empty && f == (Node)nodeList[0];
  @   ensures
  @     nodeList == \old(nodeList[1..nodeList.length]) &&
  @     \result == \old(f.item);
  @*/
private /*@ nullable @*/ Object unlinkFirst(Node f)
{
    //@ set nodeList = \dl_seqSub(nodeList,1,\dl_seqLen(nodeList));
    final Object element = f.item;
    final Node next = f.next;
    f.item = null;
    f.next = null;
    first = next;
    if (next == null) last = null;
    else next.prev = null;
    size--;
    modCount++;
    return element;
}

/*@
  @ private normal_behavior
  @   requires
  @     nodeList != \seq_empty &&
  @     l == (Node)nodeList[nodeList.length-1];
  @   ensures
  @     nodeList == \old(nodeList[0..nodeList.length-1]) &&
  @     \result == \old(l.item);
  @*/
private /*@ nullable @*/ Object unlinkLast(Node l)
{
    //@ set nodeList = \dl_seqSub(nodeList,0,\dl_seqLen(nodeList)-1);
    final Object element = l.item;
    final Node prev = l.prev;
    l.item = null;
    l.prev = null;
    last = prev;
    if (prev == null) first = null;
    else prev.next = null;
    size--;
    modCount++;
    return element;
}

/*@
  @ normal_behavior
  @   requires
  @     nodeList != \seq_empty &&
  @     0 <= nodeIndex < nodeList.length &&
  @     (Node)nodeList[nodeIndex] == x;
  @   ensures
  @     \result == \old(x.item) &&
  @     nodeList == \seq_concat(\old(nodeList)[0..nodeIndex],
  @       \old(nodeList)[nodeIndex+1..\old(nodeList).length]) &&
  @     nodeIndex == \old(nodeIndex);
  @*/
/*@ nullable @*/ Object unlink(Node x) {
    //@ set nodeList = \seq_concat(\dl_seqSub(nodeList,0,nodeIndex), \dl_seqSub(nodeList,nodeIndex+1,\dl_seqLen(nodeList)));
    final Object element = x.item;
    final Node next = x.next;
    final Node prev = x.prev;
    if (prev == null) {first = next;}
    else {
        prev.next = next;
        x.prev = null;
    }
    if (next == null) {last = prev;}
    else {
        next.prev = prev;
        x.next = null;
    }
    x.item = null;
    size--;
    modCount++;
    return element;
}

// implements java.util.Deque.getFirst
/*@
  @ also
  @ public normal_behavior
  @   requires
  @     nodeList != \seq_empty;
  @   ensures
  @     \result == ((Node)nodeList[0]).item;
  @ public exceptional_behavior
  @   requires
  @     nodeList == \seq_empty;
  @   signals_only NoSuchElementException;
  @   signals (NoSuchElementException e) true;
  @*/
public /*@ nullable strictly_pure @*/ Object getFirst() {
    final Node f = first;
    if (f == null) throw new NoSuchElementException();
    return f.item;
}

// implements java.util.Deque.getLast
/*@
  @ also
  @ public normal_behavior
  @   requires
  @     nodeList != \seq_empty;
  @   ensures
  @     \result == ((Node)nodeList[nodeList.length-1]).item;
  @ public exceptional_behavior
  @   requires
  @     nodeList == \seq_empty;
  @   signals_only NoSuchElementException;
  @   signals (NoSuchElementException e) true;
  @*/
public /*@ nullable strictly_pure @*/ Object getLast() {
    final Node l = last;
    if (l == null) throw new NoSuchElementException();
    return l.item;
}

// implements java.util.Deque.removeFirst
/*@
  @ also
  @ public normal_behavior
  @   requires
  @     nodeList != \seq_empty;
  @   ensures
  @     nodeList == \old(nodeList[1..nodeList.length]) &&
  @     \result == \old(((Node)nodeList[0]).item);
  @ public exceptional_behavior
  @   requires
  @     nodeList == \seq_empty;
  @   signals_only NoSuchElementException;
  @   signals (NoSuchElementException e) true;
  @*/
public /*@ nullable @*/ Object removeFirst() {
    final Node f = first;
    if (f == null) throw new NoSuchElementException();
    return unlinkFirst(f);
}

// implements java.util.Deque.removeLast
/*@
  @ also
  @ private normal_behavior
  @   requires
  @     nodeList != \seq_empty;
  @   ensures
  @     nodeList == \old(nodeList[0..nodeList.length-1]) &&
  @     \result ==
  @       \old(((Node)nodeList[nodeList.length-1]).item);
  @ public exceptional_behavior
  @   requires
  @     nodeList == \seq_empty;
  @   signals_only NoSuchElementException;
  @   signals (NoSuchElementException e) true;
  @*/
public /*@ nullable @*/ Object removeLast() {
    final Node l = last;
    if (l == null) throw new NoSuchElementException();
    return unlinkLast(l);
}

// new method, not in LinkedList
/*@
  @ private normal_behavior
  @   ensures \result <==> nodeList.length == Integer.MAX_VALUE;
  @*/
private /*@ strictly_pure @*/ boolean isMaxSize() {
    return size == Integer.MAX_VALUE;
}

// new method, not in LinkedList
/*@
  @ private exceptional_behavior
  @   requires nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @ private normal_behavior
  @   requires nodeList.length != Integer.MAX_VALUE;
  @   ensures true;
  @*/
private /*@ strictly_pure @*/ void checkSize() {
    if (isMaxSize())
        throw new IllegalStateException("Not enough space left in List to add new elements");
}

/*@
  @ private exceptional_behavior
  @   requires c == null;
  @   signals_only NullPointerException;
  @   signals (NullPointerException e) true;
  @ private normal_behavior
  @   requires c != null;
  @   ensures
  @     \result <==> 0 <= c.size() && c.size() <=
  @       (\bigint)Integer.MAX_VALUE - nodeList.length;
  @*/
private /*@ strictly_pure @*/ boolean
enoughSpace(/*@ nullable @*/ Collection c) {
    return 0 <= c.size() && c.size() <= Integer.MAX_VALUE - size;
} // skipped

/*@
  @ private exceptional_behavior
  @   requires
  @     c == null;
  @   signals_only NullPointerException;
  @   signals (NullPointerException e) true;
  @ private exceptional_behavior
  @   requires
  @     c != null &&
  @     !(0 <= c.size() && c.size() <=
  @       (\bigint)Integer.MAX_VALUE - nodeList.length);
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @ private normal_behavior
  @   requires
  @     c != null && 0 <= c.size() && c.size() <=
  @       (\bigint)Integer.MAX_VALUE - nodeList.length;
  @   ensures true;
  @*/
private /*@ strictly_pure @*/ void
checkSize(/*@ nullable @*/ Collection c) {
    if (!enoughSpace(c))
        throw new IllegalStateException("Not enough space left in List to add new elements");
} // skipped

// implements java.util.Deque.addFirst
/*@
  @ also
  @ public normal_behavior
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\seq_singleton(nodeList[0]),
  @       \old(nodeList)) &&
  @     ((Node)nodeList[0]).item == e;
  @ public exceptional_behavior
  @   requires
  @     nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @*/
public void addFirst(/*@ nullable @*/ Object e) {
    checkSize(); // new
    linkFirst(e);
}

// implements java.util.Deque.addLast
/*@
  @ also
  @ public normal_behavior
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\old(nodeList),
  @       \seq_singleton(nodeList[nodeList.length-1])) &&
  @     ((Node)nodeList[nodeList.length-1]).item == e;
  @ public exceptional_behavior
  @   requires
  @     nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @*/
public void addLast(/*@ nullable @*/ Object e) {
    checkSize(); // new
    linkLast(e);
}

// implements java.util.Collection.contains
/*@
  @ also
  @ public normal_behavior
  @   requires o == null;
  @   ensures
  @     \result == false ==>
  @       (\forall \bigint i; 0 <= i < nodeList.length;
  @         ((Node)nodeList[i]).item != null);
  @   ensures
  @     \result == true ==>
  @       (\exists \bigint j; 0 <= j < nodeList.length;
  @         (\forall \bigint i; 0 <= i < j;
  @           ((Node)nodeList[i]).item != null) &&
  @         ((Node)nodeList[j]).item == null);
  @ public normal_behavior
  @   requires o != null;
  @   ensures
  @     \result == false ==>
  @       (\forall \bigint i; 0 <= i < nodeList.length;
  @         !o.equals(((Node)nodeList[i]).item));
  @   ensures
  @     \result == true ==>
  @       (\exists \bigint j; 0 <= j < nodeList.length;
  @         (\forall \bigint i; 0 <= i < j;
  @           !o.equals(((Node)nodeList[i]).item)) &&
  @         o.equals(((Node)nodeList[j]).item));
  @*/
public /*@ strictly_pure @*/ boolean
contains(/*@ nullable @*/ Object o) {
    return indexOf(o) != -1;
}

// implements java.util.Collection.size
/*@
  @ also
  @ public normal_behavior
  @   ensures
  @     \result == nodeList.length;
  @*/
public /*@ strictly_pure @*/ int size() {
    return size;
}

// implements java.util.Collection.add
/*@
  @ also
  @ public normal_behavior
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\old(nodeList),
  @       \seq_singleton(nodeList[nodeList.length-1])) &&
  @     ((Node)nodeList[nodeList.length-1]).item == e &&
  @     \result;
  @ public exceptional_behavior
  @   requires
  @     nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @*/
public boolean add(/*@ nullable @*/ Object e) {
    checkSize(); // new
    linkLast(e);
    return true;
}

// implements java.util.Collection.remove
/*@
  @ also
  @ public normal_behavior
  @   requires o == null;
  @   ensures
  @     \result == false ==>
  @       (\forall \bigint i; 0 <= i < \old(nodeList.length);
  @         \old(((Node)nodeList[i]).item) != null) &&
  @       nodeList == \old(nodeList);
  @   ensures
  @     \result == true ==>
  @       (\exists \bigint j; 0 <= j < \old(nodeList.length);
  @         (\forall \bigint i; 0 <= i < j;
  @           \old(((Node)nodeList[i]).item) != null) &&
  @         nodeList == \seq_concat(\old(nodeList)[0..j],
  @           \old(nodeList)[j+1..\old(nodeList.length)]) &&
  @         \old(((Node)nodeList[j]).item) == null);
  @ public normal_behavior
  @   requires o != null;
  @   ensures
  @     \result == false ==>
  @       (\forall \bigint i; 0 <= i < \old(nodeList.length);
  @         !\old(o.equals(((Node)nodeList[i]).item))) &&
  @       nodeList == \old(nodeList);
  @   ensures
  @     \result == true ==>
  @       (\exists \bigint j; 0 <= j < \old(nodeList.length);
  @         (\forall \bigint i; 0 <= i < j;
  @           !\old(o.equals(((Node)nodeList[i]).item))) &&
  @         nodeList == \seq_concat(\old(nodeList)[0..j],
  @           \old(nodeList)[j+1..\old(nodeList.length)]) &&
  @       \old(o.equals(((Node)nodeList[j]).item)));
  @*/
public boolean remove(/*@ nullable @*/ Object o) {
    //@ ghost \bigint index = -1;
    if (o == null) {
        /*@
          @ maintaining
          @   0 <= (index + 1) &&
          @   (index + 1) <= nodeList.length;
          @ maintaining
          @   (\forall \bigint i; 0 <= i < (index + 1);
          @       ((Node)nodeList[i]).item != null);
          @ maintaining
          @   (index + 1) < nodeList.length ==>
          @     x == nodeList[index + 1];
          @ maintaining
          @   (index + 1) == nodeList.length <==>
          @   x == null;
          @ decreasing
          @   nodeList.length - (index + 1);
          @ assignable
          @   \strictly_nothing;
          @*/
        for (Node x = first; x != null; x = x.next) {
            //@ set index = index + 1;
            if (x.item == null) {
                //@ set nodeIndex = index;
                unlink(x);
                return true;
            }
        }
    } else {
        /*@
          @ maintaining
          @   0 <= (index + 1) &&
          @   (index + 1) <= nodeList.length;
          @ maintaining
          @   (\forall \bigint i; 0 <= i < (index + 1);
          @       !o.equals(((Node)nodeList[i]).item));
          @ maintaining
          @   (index + 1) < nodeList.length ==>
          @     x == nodeList[index + 1];
          @ maintaining
          @   (index + 1) == nodeList.length <==>
          @   x == null;
          @ decreasing
          @   nodeList.length - (index + 1);
          @ assignable
          @   \strictly_nothing;
          @*/
        for (Node x = first; x != null; x = x.next) {
            //@ set index = index + 1;
            if (o.equals(x.item)) {
                //@ set nodeIndex = index;
                unlink(x);
                return true;
            }
        }
    }
    return false;
}

// implements java.util.Collection.addAll
/*@
  @ also
  @ public exceptional_behavior
  @   requires
  @     c == null;
  @   signals_only NullPointerException;
  @   signals (NullPointerException e) true;
  @ public exceptional_behavior
  @   requires
  @     c != null && !(0 <= c.size() && c.size() <=
  @       (\bigint)Integer.MAX_VALUE - nodeList.length);
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @ public normal_behavior
  @   requires
  @     c != null && 0 < c.size() && c.size() <=
  @       (\bigint)Integer.MAX_VALUE - nodeList.length;
  @   ensures
  @     \result &&
  @     nodeList == \seq_concat(\old(nodeList),
  @       \dl_array2seq(c.toArray()));
  @ public normal_behavior
  @   requires
  @     c != null && c.size() == 0;
  @   ensures
  @     !\result && nodeList == \old(nodeList);
  @*/
public boolean addAll(/*@ nullable @*/ Collection c) {
    return addAll(size, c);
} // skipped

// implements java.util.Collection.addAll
/*@
  @ also
  @ public exceptional_behavior
  @   requires
  @     c == null;
  @   signals_only NullPointerException;
  @   signals (NullPointerException e) true;
  @ public exceptional_behavior
  @   requires
  @     c != null && !(0 <= c.size() && c.size() <=
  @       (\bigint)Integer.MAX_VALUE - nodeList.length);
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @ public exceptional_behavior
  @   requires
  @     index < 0 || index > nodeList.length;
  @   signals_only IndexOutOfBoundsException;
  @   signals (IndexOutOfBoundsException e) true;      
  @ public normal_behavior
  @   requires
  @     c != null && 0 < c.size() && c.size() <=
  @       (\bigint)Integer.MAX_VALUE - nodeList.length &&
  @     0 <= index && index <= nodeList.length;
  @   ensures
  @     \result &&
  @     nodeList == \seq_concat(\old(nodeList)[0..index],
  @       \seq_concat(\dl_array2seq(c.toArray()),
  @         \old(nodeList[index..nodeList.length])));
  @ public normal_behavior
  @   requires
  @     c != null && c.size() == 0 &&
  @     0 <= index && index <= nodeList.length;
  @   ensures
  @     !\result && nodeList == \old(nodeList);
  @*/
public boolean addAll(int index,/*@ nullable @*/ Collection c)
{   //@ ghost \seq seqSub_x;
    //@ ghost \seq seqSub_y;
    //@ ghost \seq seqSub_z;
    checkSize(c); // new
    checkPositionIndex(index);

    Object[] a = c.toArray();
    int numNew = a.length;
    if (numNew == 0)
        return false;

    Node pred, succ;
    if (index == size) {
        succ = null;
        pred = last;
    } else {
        succ = node(index);
        pred = succ.prev;
    }

    for (Object o : a) {
        @SuppressWarnings("unchecked")
        java.lang.Object e = (java.lang.Object) o;
        Node newNode = new Node(pred, e, null);
        if (pred == null)
            first = newNode;
        else
            pred.next = newNode;
        pred = newNode;
    }

    if (succ == null) {
        last = pred;
    } else {
        pred.next = succ;
        succ.prev = pred;
    }
    //@ set seqSub_x = \dl_seqSub(nodeList,0,index);
    //@ set seqSub_y = \dl_array2seq(c.toArray());
    //@ set seqSub_z = \dl_seqSub(nodeList,index,\dl_seqLen(nodeList));
    //@ set nodeList = \seq_concat(seqSub_x,\seq_concat(seqSub_y,seqSub_z));
    size += numNew;
    modCount++;
    return true;
} // skipped

// implements java.util.Collection.clear
/*@
  @ also
  @ public normal_behavior 
  @   ensures
  @     nodeList == \seq_empty &&
  @     (\forall \bigint i; 0 <= i < \old(nodeList.length);
  @       ((Node)\old(nodeList[i])).prev == null &&
  @       ((Node)\old(nodeList[i])).item == null &&
  @       ((Node)\old(nodeList[i])).next == null);
  @*/
public void clear() {
    //@ ghost \bigint index;
    //@ set index = 0;
    /*@ 
      @ maintaining
      @   0 <= index && index <= nodeList.length;
      @ maintaining
      @   x != null ==> index < nodeList.length;
      @ maintaining
      @   index < nodeList.length ==> x == nodeList[index];
      @ maintaining
      @   (\forall \bigint i; index<=i<nodeList.length-1;
      @     ((Node)nodeList[i]).next==(Node)nodeList[i+1]);
      @ maintaining
      @   nodeList.length > 0 ==>
      @     ((Node)nodeList[nodeList.length-1]).next == null;
      @ maintaining
      @   nodeList == \old(nodeList);
      @ maintaining
      @   (\forall \bigint i; 0 <= i < index;
      @     ((Node)nodeList[i]).prev == null &&
      @     ((Node)nodeList[i]).item == null &&
      @     ((Node)nodeList[i]).next == null);
      @ maintaining
      @   (\forall \bigint i; index <= i < nodeList.length;
      @     ((Node)nodeList[i]).prev ==
      @       \old(((Node)nodeList[i]).prev) &&
      @     ((Node)nodeList[i]).item ==
      @       \old(((Node)nodeList[i]).item) &&
      @     ((Node)nodeList[i]).next ==
      @       \old(((Node)nodeList[i]).next));
      @ decreasing
      @   nodeList.length - index;
      @*/
    for (Node x = first; x != null;) {
        Node next = x.next;
        x.item = null;
        x.next = null;
        x.prev = null;
        //@ set index = index + 1;
        x = next;
    }
    first = last = null;
    size = 0;
    //@ set nodeList = \seq_empty;
    modCount++;
}

// implements java.util.List.get
/*@
  @ also
  @ public normal_behavior
  @   requires
  @     0 <= index < nodeList.length;
  @   ensures
  @     \result == ((Node)nodeList[index]).item;
  @ public exceptional_behavior
  @   requires
  @     index < 0 || index >= nodeList.length;
  @   signals_only IndexOutOfBoundsException;
  @   signals (IndexOutOfBoundsException e) true;
  @*/
public /*@ nullable strictly_pure @*/ Object get(int index) {
    checkElementIndex(index);
    return node(index).item;
}

// implements java.util.List.set
/*@
  @ also
  @ public normal_behavior
  @   requires
  @     0 <= index < nodeList.length;
  @   ensures
  @     ((Node)nodeList[index]).item == element &&
  @     nodeList == \old(nodeList) &&
  @     \result == \old(((Node)nodeList[index]).item);
  @ public exceptional_behavior
  @   requires
  @     index < 0 || index >= nodeList.length;
  @   signals_only IndexOutOfBoundsException;
  @   signals (IndexOutOfBoundsException e) true;
  @*/
public /*@ nullable @*/ Object
set(int index, /*@ nullable @*/ Object element) {
    checkElementIndex(index);
    Node x = node(index);
    Object oldVal = x.item;
    x.item = element;
    return oldVal;
}

// implements java.util.List.add
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE &&
  @     0 <= index && index <= nodeList.length;
  @   ensures
  @     ((Node)nodeList[index]).item == element &&
  @     nodeList == \seq_concat(\old(nodeList[0..index]),
  @       \seq_concat(\seq_singleton(nodeList[index]),
  @         \old(nodeList[index..nodeList.length])));
  @ public exceptional_behavior 
  @   requires nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @ public exceptional_behavior 
  @   requires
  @     (index < 0 || index > nodeList.length) &&
  @     nodeList.length != Integer.MAX_VALUE;
  @   signals_only IndexOutOfBoundsException;
  @   signals (IndexOutOfBoundsException e) true;
  @*/
public void add(int index, /*@ nullable @*/ Object element) {
    checkSize(); // new
    checkPositionIndex(index);
    //@ set nodeIndex = index;
    if (index == size) linkLast(element);
    else linkBefore(element, node(index));
}

// implements java.util.List.remove
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     0 <= index < nodeList.length;
  @   ensures
  @     nodeList == \old(\seq_concat(nodeList[0..index],
  @       nodeList[index+1..nodeList.length])) &&
  @     \result == \old(((Node)nodeList[index]).item);
  @ public exceptional_behavior 
  @   requires
  @     index < 0 || index >= nodeList.length;
  @   signals_only IndexOutOfBoundsException;
  @   signals (IndexOutOfBoundsException e) true;
  @*/
public /*@ nullable @*/ Object remove(int index) {
    checkElementIndex(index);
    //@ set nodeIndex = index;
    return unlink(node(index));
}

/*@
  @ private normal_behavior 
  @   ensures
  @     \result <==> 0 <= index < nodeList.length;
  @*/
private /*@ strictly_pure @*/ boolean
isElementIndex(int index) {
    return index >= 0 && index < size;
}

/*@
  @ private normal_behavior 
  @   ensures
  @     \result <==> 0 <= index && index <= nodeList.length;
  @*/
private /*@ strictly_pure @*/ boolean
isPositionIndex(int index) {
    return index >= 0 && index <= size;
}

/*@
  @ private normal_behavior
  @   requires true;
  @ ensures true;
  @   assignable \strictly_nothing;
  @*/
private /*@ strictly_pure @*/ String outOfBoundsMsg(int index) {
    return "Index: " + index + ", Size: " + size;
}

/*@
  @ private exceptional_behavior 
  @   requires
  @     index < 0 || index >= nodeList.length;
  @   signals_only IndexOutOfBoundsException;
  @   signals (IndexOutOfBoundsException e) true;
  @ private normal_behavior 
  @   requires
  @     0 <= index < nodeList.length;
  @   ensures
  @     true;
  @*/
private /*@ strictly_pure @*/ void
checkElementIndex(int index) {
    if (!isElementIndex(index))
        throw new IndexOutOfBoundsException(
            outOfBoundsMsg(index));
}

/*@
  @ private exceptional_behavior 
  @   requires
  @     index < 0 || index > nodeList.length;
  @   signals_only IndexOutOfBoundsException;
  @   signals (IndexOutOfBoundsException e) true;
  @ private normal_behavior 
  @   requires
  @     0 <= index && index <= nodeList.length;
  @   ensures
  @     true;
  @*/
private /*@ strictly_pure @*/ void
checkPositionIndex(int index) {
    if (!isPositionIndex(index))
        throw new IndexOutOfBoundsException(
            outOfBoundsMsg(index));
}

/*@
  @ normal_behavior 
  @   requires
  @     0 <= index < nodeList.length;
  @   ensures
  @     \result == nodeList[index];
  @*/
/*@ strictly_pure @*/ Node node(int index) {
    if (index < (size >> 1)) {
        Node x = first;
        /*@ 
          @ maintaining
          @   x != null && 0 <= i && i <= index &&
          @   x == (Node)nodeList[i];
          @ decreasing
          @   index - i;
          @ assignable
          @   \strictly_nothing;
          @*/
        for (int i = 0; i < index; i++) 
            x = x.next;
        return x;
    } else {
        Node x = last;
        /*@ 
          @ maintaining
          @   x != null && index <= i && i <= size - 1 &&
          @   x == (Node)nodeList[i];
          @ decreasing
          @   i - index;
          @ assignable
          @   \strictly_nothing;
          @*/
        for (int i = size - 1; i > index; i--)
            x = x.prev;
        return x;
    }
}

// implements java.util.List.indexOf
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     o == null;
  @   ensures
  @     \result >= -1 && \result < nodeList.length;
  @   ensures
  @     \result == -1 ==>
  @       (\forall \bigint i; 0 <= i < nodeList.length;
  @         ((Node)nodeList[i]).item != null);
  @   ensures
  @     \result >= 0 && \result < nodeList.length ==>
  @       (\forall \bigint i; 0 <= i < \result;
  @         ((Node)nodeList[i]).item != null) &&
  @       ((Node)nodeList[\result]).item == null;
  @ public normal_behavior 
  @   requires
  @     o != null;
  @   ensures
  @     \result >= -1 && \result < nodeList.length;
  @   ensures
  @     \result == -1 ==>
  @       (\forall \bigint i; 0 <= i < nodeList.length;
  @         !o.equals(((Node)nodeList[i]).item));
  @   ensures
  @     \result >= 0 && \result < nodeList.length ==>
  @       (\forall \bigint i; 0 <= i < \result;
  @         !o.equals(((Node)nodeList[i]).item)) &&
  @       o.equals(((Node)nodeList[\result]).item);
  @*/
public /*@ strictly_pure @*/ int
indexOf(/*@ nullable @*/ Object o) {
    int index = 0;
    if (o == null) {
        /*@ 
          @ maintaining
          @   (\forall \bigint i; 0 <= i < index;
          @       ((Node)nodeList[i]).item != null);
          @ maintaining
          @   0 <= index && index <= nodeList.length;
          @ maintaining
          @   0 <= index && index < nodeList.length ==>
          @     x == (Node)nodeList[index];
          @ maintaining
          @   index == nodeList.length <==> x == null;
          @ decreasing
          @   nodeList.length - index;
          @ assignable
          @   \strictly_nothing;
          @*/
        for (Node x = first; x != null; x = x.next) {
            if (x.item == null)
                return index;
            index++;
        }
    } else {
        /*@
          @ maintaining
          @   (\forall \bigint i; 0 <= i < index;
          @       !o.equals(((Node)nodeList[i]).item));
          @ maintaining
          @   0 <= index && index <= nodeList.length;
          @ maintaining
          @   0 <= index && index < nodeList.length ==>
          @     x == (Node)nodeList[index];
          @ maintaining
          @   index == nodeList.length <==> x == null;
          @ decreasing
          @   nodeList.length - index;
          @ assignable
          @   \strictly_nothing;
          @*/
        for (Node x = first; x != null; x = x.next) {
            if (o.equals(x.item))
                return index;
            index++;
        }
    }
    return -1;
}

// implements java.util.List.lastIndexOf
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     o == null;
  @   ensures
  @     \result >= -1 && \result < nodeList.length;
  @   ensures
  @     \result == -1 ==>
  @       (\forall \bigint i; 0 <= i < nodeList.length;
  @         ((Node)nodeList[i]).item != null);
  @   ensures
  @     \result >= 0 ==>
  @       (\forall \bigint i; \result < i < nodeList.length;
  @         ((Node)nodeList[i]).item != null) &&
  @       ((Node)nodeList[\result]).item == null;
  @ public normal_behavior 
  @   requires
  @     o != null;
  @   ensures
  @     \result >= -1 && \result < nodeList.length;
  @   ensures
  @     \result == -1 ==>
  @       (\forall \bigint i; 0 <= i < nodeList.length;
  @         !o.equals(((Node)nodeList[i]).item));
  @   ensures
  @     \result >= 0 ==>
  @       (\forall \bigint i; \result < i < nodeList.length;
  @         !o.equals(((Node)nodeList[i]).item)) &&
  @       o.equals(((Node)nodeList[\result]).item);
  @*/
public /*@ strictly_pure @*/ int
lastIndexOf(/*@ nullable @*/ Object o) {
    int index = size;
    if (o == null) {
        /*@
          @ maintaining
          @   (\forall \bigint i; index <= i < nodeList.length;
          @       ((Node)nodeList[i]).item != null);
          @ maintaining
          @   0 <= index && index <= nodeList.length;
          @ maintaining
          @   0 < index && index <= nodeList.length ==>
          @     x == (Node)nodeList[index - 1];
          @ maintaining
          @   index == 0 <==> x == null;
          @ decreasing
          @   index;
          @ assignable
          @   \strictly_nothing;
          @*/
        for (Node x = last; x != null; x = x.prev) {
            index--;
            if (x.item == null)
                return index;
        }
    } else {
        /*@
          @ maintaining
          @   (\forall \bigint i; index <= i < nodeList.length;
          @       !o.equals(((Node)nodeList[i]).item));
          @ maintaining
          @   0 <= index && index <= nodeList.length;
          @ maintaining
          @   0 < index && index <= nodeList.length ==>
          @     x == (Node)nodeList[index - 1];
          @ maintaining
          @   index == 0 <==> x == null;
          @ decreasing
          @   index;
          @ assignable
          @   \strictly_nothing;
          @*/
        for (Node x = last; x != null; x = x.prev) {
            index--;
            if (o.equals(x.item))
                return index;
        }
    }
    return -1;
}

// implements java.util.Deque.peek
/*@
  @ also
  @ public normal_behavior 
  @   ensures
  @     \result == (\old(nodeList) == \seq_empty ? null :
  @       ((Node)nodeList[0]).item);
  @*/
public /*@ nullable strictly_pure @*/ Object peek() {
    final Node f = first;
    return (f == null) ? null : f.item;
}

// implements java.util.Deque.element
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     nodeList != \seq_empty;
  @   ensures
  @     \result == ((Node)nodeList[0]).item;
  @ public exceptional_behavior 
  @   requires
  @     nodeList == \seq_empty;
  @   signals_only NoSuchElementException;
  @   signals (NoSuchElementException e) true;
  @*/
public /*@ nullable strictly_pure @*/ Object element() {
    return getFirst();
}

// implements java.util.Deque.poll
/*@
  @ also
  @ public normal_behavior 
  @   ensures
  @     nodeList == \old(nodeList[1..nodeList.length]) &&
  @     \result == (\old(nodeList) == \seq_empty ? null :
  @       \old(((Node)nodeList[0]).item));
  @*/
public /*@ nullable @*/ Object poll() {
    final Node f = first;
    return (f == null) ? null : unlinkFirst(f);
}

// implements java.util.Deque.remove
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     nodeList != \seq_empty;
  @   ensures
  @     nodeList == \old(nodeList[1..nodeList.length]) &&
  @     \result == \old(((Node)nodeList[0]).item);
  @ public exceptional_behavior
  @   requires
  @     nodeList == \seq_empty;
  @   signals_only NoSuchElementException;
  @   signals (NoSuchElementException e) true;
  @*/
public /*@ nullable @*/ Object remove() {
    return removeFirst();
}

// implements java.util.Deque.offer
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\old(nodeList),
  @       \seq_singleton(nodeList[nodeList.length-1])) &&
  @     ((Node)nodeList[nodeList.length-1]).item == e &&
  @     \result;
  @ public exceptional_behavior 
  @   requires
  @     nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @*/
public boolean offer(/*@ nullable @*/ Object e) {
    return add(e);
}

// implements java.util.Deque.offerFirst
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\seq_singleton(nodeList[0]),
  @       \old(nodeList)) &&
  @     ((Node)nodeList[0]).item == e &&
  @     \result;
  @ public exceptional_behavior 
  @   requires
  @     nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @*/
public boolean offerFirst(/*@ nullable @*/ Object e) {
    addFirst(e);
    return true;
}

// implements java.util.Deque.offerLast
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\old(nodeList),
  @       \seq_singleton(nodeList[nodeList.length-1])) &&
  @     ((Node)nodeList[nodeList.length-1]).item == e &&
  @     \result;
  @ public exceptional_behavior 
  @   requires
  @     nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @*/
public boolean offerLast(/*@ nullable @*/ Object e) {
    addLast(e);
    return true;
}

// implements java.util.Deque.peekFirst
/*@
  @ also
  @ public normal_behavior 
  @   ensures
  @     \result == (\old(nodeList) == \seq_empty ? null :
  @       ((Node)nodeList[0]).item);
  @*/
public /*@ nullable strictly_pure @*/ Object peekFirst() {
    final Node f = first;
    return (f == null) ? null : f.item;
}

// implements java.util.Deque.peekLast
/*@
  @ also
  @ public normal_behavior 
  @   ensures
  @     \result == (\old(nodeList) == \seq_empty ? null :
  @       ((Node)nodeList[nodeList.length-1]).item);
  @*/
public /*@ nullable strictly_pure @*/ Object peekLast() {
    final Node l = last;
    return (l == null) ? null : l.item;
}

// implements java.util.Deque.pollFirst
/*@
  @ also
  @ public normal_behavior 
  @   ensures
  @     nodeList == \old(nodeList[1..nodeList.length]) &&
  @     \result == (\old(nodeList) == \seq_empty ? null :
  @       \old(((Node)nodeList[0]).item));
  @*/
public /*@ nullable @*/ Object pollFirst() {
    final Node f = first;
    return (f == null) ? null : unlinkFirst(f);
}

// implements java.util.Deque.pollLast
/*@
  @ also
  @ public normal_behavior 
  @   ensures
  @     nodeList == \old(nodeList[0..nodeList.length-1]) &&
  @     \result == (\old(nodeList) == \seq_empty ? null :
  @       \old(((Node)nodeList[nodeList.length-1]).item));
  @*/
public /*@ nullable @*/ Object pollLast() {
    final Node l = last;
    return (l == null) ? null : unlinkLast(l);
}

// implements java.util.Deque.push
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\seq_singleton(nodeList[0]),
  @       \old(nodeList)) &&
  @     ((Node)nodeList[0]).item == e;
  @ public exceptional_behavior 
  @   requires
  @     nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @*/
public void push(/*@ nullable @*/ Object e) {
    addFirst(e);
}

// implements java.util.Deque.pop
/*@
  @ also
  @ public normal_behavior 
  @   requires
  @     nodeList != \seq_empty;
  @   ensures
  @     nodeList == \old(nodeList[1..nodeList.length]) &&
  @     \result == \old(((Node)nodeList[0]).item);
  @ public exceptional_behavior 
  @   requires
  @     nodeList == \seq_empty;
  @   signals_only NoSuchElementException;
  @   signals (NoSuchElementException e) true;
  @*/
public /*@ nullable @*/ Object pop() {
    return removeFirst();
}

// implements java.util.Deque.removeFirstOccurrence
/*@
  @ also
  @ public normal_behavior
  @   requires o == null;
  @   ensures
  @     \result == false ==>
  @       (\forall \bigint i; 0 <= i < \old(nodeList.length);
  @         \old(((Node)nodeList[i]).item) != null) &&
  @       nodeList == \old(nodeList);
  @   ensures
  @     \result == true ==>
  @       (\exists \bigint j; 0 <= j < \old(nodeList.length);
  @         (\forall \bigint i; 0 <= i < j;
  @           \old(((Node)nodeList[i]).item) != null) &&
  @         nodeList == \seq_concat(\old(nodeList)[0..j],
  @           \old(nodeList)[j+1..\old(nodeList.length)]) &&
  @         \old(((Node)nodeList[j]).item) == null);
  @ public normal_behavior
  @   requires o != null;
  @   ensures
  @     \result == false ==>
  @       (\forall \bigint i; 0 <= i < \old(nodeList.length);
  @         !\old(o.equals(((Node)nodeList[i]).item))) &&
  @       nodeList == \old(nodeList);
  @   ensures
  @     \result == true ==>
  @       (\exists \bigint j; 0 <= j < \old(nodeList.length);
  @         (\forall \bigint i; 0 <= i < j;
  @           !\old(o.equals(((Node)nodeList[i]).item))) &&
  @         nodeList == \seq_concat(\old(nodeList)[0..j],
  @           \old(nodeList)[j+1..\old(nodeList.length)]) &&
  @       \old(o.equals(((Node)nodeList[j]).item)));
  @*/
public boolean removeFirstOccurrence(
/*@ nullable @*/ Object o) { return remove(o);
}


// implements java.util.Deque.removeLastOccurrence
/*@
  @ also
  @ public normal_behavior
  @   requires o == null;
  @   ensures
  @     \result == false ==>
  @       (\forall \bigint i; 0 <= i < \old(nodeList.length);
  @         \old(((Node)nodeList[i]).item) != null) &&
  @       nodeList == \old(nodeList);
  @   ensures
  @     \result == true ==>
  @       (\exists \bigint j; 0 <= j < \old(nodeList.length);
  @         (\forall \bigint i; j < i < \old(nodeList.length);
  @           \old(((Node)nodeList[i]).item) != null) &&
  @         nodeList == \seq_concat(\old(nodeList)[0..j],
  @           \old(nodeList)[j+1..\old(nodeList.length)]) &&
  @         \old(((Node)nodeList[j]).item) == null);
  @ public normal_behavior
  @   requires o != null;
  @   ensures
  @     \result == false ==>
  @       (\forall \bigint i; 0 <= i < \old(nodeList.length);
  @         !\old(o.equals(((Node)nodeList[i]).item))) &&
  @       nodeList == \old(nodeList);
  @   ensures
  @     \result == true ==>
  @       (\exists \bigint j; 0 <= j < \old(nodeList.length);
  @         (\forall \bigint i; j < i < \old(nodeList.length);
  @           !\old(o.equals(((Node)nodeList[i]).item))) &&
  @         nodeList == \seq_concat(\old(nodeList)[0..j],
  @           \old(nodeList)[j+1..\old(nodeList.length)]) &&
  @       \old(o.equals(((Node)nodeList[j]).item)));
  @*/

public boolean removeLastOccurrence(/*@ nullable @*/ Object o) {
//@ ghost \bigint index = size;
if (o == null) {
        /*@
          @ maintaining
          @   0 <= index && index <= nodeList.length;
          @ maintaining
          @   (\forall \bigint i; index <= i < nodeList.length;
          @       ((Node)nodeList[i]).item != null);
          @ maintaining
          @   0 < index && index <= nodeList.length ==>
          @     x == (Node)nodeList[index - 1];
          @ maintaining
          @   index == 0 <==> x == null;
          @ decreasing
          @   index;
          @ assignable
          @   \strictly_nothing;
          @*/
    for (Node x = last; x != null; x = x.prev) {
        //@ set index = index - 1;
        if (x.item == null) {
            //@ set nodeIndex = index;
            unlink(x);
            return true;
        }
    }
} else {
        /*@
          @ maintaining
          @   0 <= index && index <= nodeList.length;
          @ maintaining
          @   (\forall \bigint i; index <= i < nodeList.length;
          @       !o.equals(((Node)nodeList[i]).item));
          @ maintaining
          @   0 < index && index <= nodeList.length ==>
          @     x == (Node)nodeList[index - 1];
          @ maintaining
          @   index == 0 <==> x == null;
          @ decreasing
          @   index;
          @ assignable
          @   \strictly_nothing;
          @*/
    for (Node x = last; x != null; x = x.prev) {
        //@ set index = index - 1;
        if (o.equals(x.item)) {
            //@ set nodeIndex = index;
            unlink(x);
            return true;
        }
    }
}
return false;
}

// implements java.util.List.listIterator
public ListIterator listIterator(int index) {
    checkPositionIndex(index);
    return new ListItr(index);
} // skipped

private class ListItr implements ListIterator {
    private Node lastReturned =  null;
    private Node next;
    private int nextIndex;
    private int expectedModCount =  modCount;

    ListItr(int index) {
        next = (index == size) ? null : node(index);
        nextIndex = index;
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     \result <==> nextIndex < nodeList.length;
      @*/
    public /*@ strictly_pure @*/ boolean hasNext() {
        return nextIndex < size;
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     true;
      @*/
    public /*@ nullable @*/ java.lang.Object next() {
        checkForComodification();
        if (!hasNext())
            throw new NoSuchElementException();

        lastReturned = next;
        next = next.next;
        nextIndex++;
        return lastReturned.item;
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     \result <==> nextIndex > 0;
      @*/
    public /*@ strictly_pure @*/ boolean hasPrevious() {
        return nextIndex > 0;
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     true;
      @*/
    public /*@ nullable @*/ java.lang.Object previous() {
        checkForComodification();
        if (!hasPrevious())
            throw new NoSuchElementException();

        lastReturned = next = (next == null) ? last : next.prev;
        nextIndex--;
        return lastReturned.item;
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     true;
      @*/
    public int nextIndex() {
        return nextIndex;
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     true;
      @*/
    public int previousIndex() {
        return nextIndex - 1;
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     true;
      @*/
    public void remove() {
        checkForComodification();
        if (lastReturned == null)
            throw new IllegalStateException();

        Node lastNext =  lastReturned.next;
        unlink(lastReturned);
        if (next == lastReturned)
            next = lastNext;
         else
            nextIndex--;
        lastReturned = null;
        expectedModCount++;
    }

    public void set(/*@ nullable @*/ java.lang.Object e) {
        if (lastReturned == null)
            throw new IllegalStateException();
        checkForComodification();
        lastReturned.item = e;
    }

    public void add(/*@ nullable @*/ java.lang.Object e) {
        checkForComodification();
        lastReturned = null;
        if (next == null)
            linkLast(e);
         else
            linkBefore(e, next);
        nextIndex++;
        expectedModCount++;
    }

    public void forEachRemaining(Consumer action) {
        Objects.requireNonNull(action);
        while (modCount == expectedModCount && nextIndex < size)
         {
            action.accept(next.item);
            lastReturned = next;
            next = next.next;
            nextIndex++;
        }
        checkForComodification();
    }

    final void checkForComodification() {
        if (modCount != expectedModCount)
            throw new ConcurrentModificationException();
    }
}

private static class Node {
    /*@ invariant
      @   (this.next != null ==> this.next.prev == this) &&
      @   (this.prev != null ==> this.prev.next == this);
      @*/

    /*@ nullable @*/ Object item;
    /*@ nullable @*/ Node next;
    /*@ nullable @*/ Node prev;

    Node(/*@ nullable @*/ Node prev,
    /*@ nullable @*/ Object element,
    /*@ nullable @*/ Node next) {
        this.item = element;
        this.next = next;
        this.prev = prev;
    }
}

public Iterator descendingIterator() {
    return new DescendingIterator();
} // skipped

private class DescendingIterator implements Iterator {
    private final ListItr itr = new ListItr(size());

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     true;
      @*/
    public boolean hasNext() {
        return itr.hasPrevious();
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     true;
      @*/
    public java.lang.Object next() {
        return itr.previous();
    }

    /*@
      @ also
      @ public normal_behavior
      @   ensures
      @     true;
      @*/
    public void remove() {
        itr.remove();
    }
}

private BoundedLinkedList superClone() {
    try {
        return (BoundedLinkedList) super.clone();
    } catch (CloneNotSupportedException e) {
        throw new InternalError(e);
    }
} // skipped

/*@
  @ also
  @ public normal_behavior
  @   ensures
  @     true;
  @*/
public Object clone() {
    BoundedLinkedList clone = superClone();
    clone.first = clone.last = null;
    clone.size = 0;
    clone.modCount = 0;
    for (Node x = first; x != null; x = x.next)
        clone.add(x.item);
    return clone;
} // skipped

// implements java.util.Collection.toArray
/*@ 
  @ also
  @ public normal_behavior
  @   ensures
  @     \result != null && \result.length == nodeList.length &&
  @     (\forall \bigint i; 0 <= i < nodeList.length;
  @       \result[i] == ((Node)nodeList[i]).item);
  @*/
/*@ nullable @*/ public Object[] toArray() {
    Object[] result = new Object[size];
    int i = 0;
    /*@ 
      @ maintaining
      @   result != null;
      @ maintaining
      @   result.length == nodeList.length;
      @ maintaining
      @   0 <= i && i <= nodeList.length;
      @ maintaining
      @   x != null ==> i < nodeList.length;
      @ maintaining
      @   i < nodeList.length ==> x == nodeList[i];
      @ maintaining
      @   nodeList == \old(nodeList);
      @ maintaining
      @   (\forall \bigint j; 0 <= j < nodeList.length;
      @     ((Node)nodeList[j]).next ==
      @     \old(((Node)nodeList[j]).next));
      @ maintaining
      @   \invariant_for(this);
      @ maintaining
      @   (\forall \bigint j; 0 <= j < result.length;
      @     result[j] == null ||
      @     result[j] instanceof Object);
      @ maintaining
      @   (\forall \bigint j; 0 <= j < i;
      @     result[j] == ((Node)nodeList[j]).item);
      @ maintaining
      @   (\forall \bigint j; i <= j < result.length;
      @     result[j] == null);
      @ decreasing
      @   nodeList.length - i;
      @*/		  
    for (Node x = first; x != null; x = x.next)
        result[i++] = x.item;
    return result;
}

public java.lang.Object[] toArray(java.lang.Object[] a) {
    if (a.length < size)
        a = (java.lang.Object[]) java.lang.reflect.Array
          .newInstance(a.getClass().getComponentType(), size);
    int i = 0;
    Object[] result = a;
    for (Node x = first; x != null; x = x.next)
        result[i++] = x.item;
    if (a.length > size)
        a[size] = null;
    return a;
} // skipped

private static final long serialVersionUID =
    876323262645176354L;

private void writeObject(java.io.ObjectOutputStream s)
throws java.io.IOException {
    s.defaultWriteObject();
    s.writeInt(size);
    for (Node x = first; x != null; x = x.next)
        s.writeObject(x.item);
} // skipped

private void readObject(java.io.ObjectInputStream s)
throws java.io.IOException, ClassNotFoundException {
    s.defaultReadObject();
    int size = s.readInt();
    for (int i = 0; i < size; i++)
        linkLast((java.lang.Object) s.readObject());
} // skipped

public Spliterator spliterator() {
     return new LLSpliterator(this, -1, 0);
} // skipped

static final class LLSpliterator implements Spliterator {
    static final int BATCH_UNIT = 1 << 10;
    static final int MAX_BATCH = 1 << 25;
    final BoundedLinkedList list;
    Node current;
    int est;
    int expectedModCount;
    int batch;

    LLSpliterator(BoundedLinkedList list, int est,
    int expectedModCount) {
        this.list = list;
        this.est = est;
        this.expectedModCount = expectedModCount;
    }

    final int getEst() {
        int s;
        final BoundedLinkedList lst;
        if ((s = est) < 0) {
            if ((lst = list) == null)
                s = est = 0;
            else {
                expectedModCount = lst.modCount;
                current = lst.first;
                s = est = lst.size;
            }
        }
        return s;
    }

    public long estimateSize() { return (long) getEst(); }

    public Spliterator trySplit() {
        Node p;
        int s = getEst();
        if (s > 1 && (p = current) != null) {
            int n = batch + BATCH_UNIT;
            if (n > s)
                n = s;
            if (n > MAX_BATCH)
                n = MAX_BATCH;
            Object[] a = new Object[n];
            int j = 0;
            do { a[j++] = p.item; }
            while ((p = p.next) != null && j < n);
            current = p;
            batch = j;
            est = s - j;
            return Spliterators.spliterator(
                a, 0, j, Spliterator.ORDERED);
        }
        return null;
    }

    public void forEachRemaining(Consumer action) {
        Node p; int n;
        if (action == null) throw new NullPointerException();
        if ((n = getEst()) > 0 && (p = current) != null) {
            current = null;
            est = 0;
            do {
                Object e = p.item;
                p = p.next;
                action.accept(e);
            } while (p != null && --n > 0);
        }
        if (list.modCount != expectedModCount)
            throw new ConcurrentModificationException();
    }

    public boolean tryAdvance(Consumer action) {
        Node p;
        if (action == null) throw new NullPointerException();
        if (getEst() > 0 && (p = current) != null) {
            --est;
            Object e = p.item;
            current = p.next;
            action.accept(e);
            if (list.modCount != expectedModCount)
                throw new ConcurrentModificationException();
            return true;
        }
        return false;
    }

    public int characteristics() {
        return Spliterator.ORDERED | Spliterator.SIZED |
            Spliterator.SUBSIZED;
    }
}

}
