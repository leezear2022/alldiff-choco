package org.chocosolver.util.objects;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.Vocabulary;
import org.antlr.v4.runtime.VocabularyImpl;
import org.antlr.v4.runtime.misc.IntSet;
import org.antlr.v4.runtime.misc.IntegerList;
import org.antlr.v4.runtime.misc.MurmurHash;

import java.util.*;

/**
 * This class implements the {@link IntSet} backed by a sorted array of
 * non-overlapping intervals. It is particularly efficient for representing
 * large collections of numbers, where the majority of elements appear as part
 * of a sequential range of numbers that are all part of the set. For example,
 * the set { 1, 2, 3, 4, 7, 8 } may be represented as { [1, 4], [7, 8] }.
 *
 * <p>
 * This class is able to represent sets containing any combination of values in
 * the range {@link Integer#MIN_VALUE} to {@link Integer#MAX_VALUE}
 * (inclusive).</p>
 */
public class IntIntervalSet implements IntSet {
    public static final IntIntervalSet COMPLETE_CHAR_SET = IntIntervalSet.of(Lexer.MIN_CHAR_VALUE, Lexer.MAX_CHAR_VALUE);

    static {
        COMPLETE_CHAR_SET.setReadonly(true);
    }

    public static final IntIntervalSet EMPTY_SET = new IntIntervalSet();

    static {
        EMPTY_SET.setReadonly(true);
    }

    /**
     * The list of sorted, disjoint intervals.
     */
    protected List<IntInterval> intervals;

    protected boolean readonly;

    public IntIntervalSet(List<IntInterval> intervals) {
        this.intervals = intervals;
    }

    public IntIntervalSet(IntIntervalSet set) {
        this();
        addAll(set);
    }

    public IntIntervalSet(int... els) {
        if (els == null) {
            intervals = new ArrayList<IntInterval>(2); // most sets are 1 or 2 elements
        } else {
            intervals = new ArrayList<IntInterval>(els.length);
            for (int e : els) add(e);
        }
    }

    /**
     * Create a set with a single element, el.
     */

    public static IntIntervalSet of(int a) {
        IntIntervalSet s = new IntIntervalSet();
        s.add(a);
        return s;
    }

    /**
     * Create a set with all ints within range [a..b] (inclusive)
     */
    public static IntIntervalSet of(int a, int b) {
        IntIntervalSet s = new IntIntervalSet();
        s.add(a, b);
        return s;
    }

    public void clear() {
        if (readonly) throw new IllegalStateException("can't alter readonly IntIntervalSet");
        intervals.clear();
    }

    /**
     * Add a single element to the set.  An isolated element is stored
     * as a range el..el.
     */
    @Override
    public void add(int el) {
        if (readonly) throw new IllegalStateException("can't alter readonly IntIntervalSet");
        add(el, el);
    }

    /**
     * Add interval; i.e., add all integers from a to b to set.
     * If b&lt;a, do nothing.
     * Keep list in sorted order (by left range value).
     * If overlap, combine ranges.  For example,
     * If this is {1..5, 10..20}, adding 6..7 yields
     * {1..5, 6..7, 10..20}.  Adding 4..8 yields {1..8, 10..20}.
     */
    public void add(int a, int b) {
        add(IntInterval.of(a, b));
    }

    // copy on write so we can cache a..a intervals and sets of that
    protected void add(IntInterval addition) {
        if (readonly) throw new IllegalStateException("can't alter readonly IntIntervalSet");
        //System.out.println("add "+addition+" to "+intervals.toString());
        if (addition.b < addition.a) {
            return;
        }
        // find position in list
        // Use iterators as we modify list in place
        for (ListIterator<IntInterval> iter = intervals.listIterator(); iter.hasNext(); ) {
            IntInterval r = iter.next();
            if (addition.equals(r)) {
                return;
            }
//            if (addition.adjacent(r) || !addition.disjoint(r)) {
            if (!addition.disjoint(r)) {
                // next to each other, make a single larger interval
                IntInterval bigger = addition.union(r);
                iter.set(bigger);
                // make sure we didn't just create an interval that
                // should be merged with next interval in list
                while (iter.hasNext()) {
                    IntInterval next = iter.next();
//                    if (!bigger.adjacent(next) && bigger.disjoint(next)) {
                    if (bigger.disjoint(next)) {
                        break;
                    }

                    // if we bump up against or overlap next, merge
                    iter.remove();   // remove this one
                    iter.previous(); // move backwards to what we just set
                    iter.set(bigger.union(next)); // set to 3 merged ones
                    iter.next(); // first call to next after previous duplicates the result
                }
                return;
            }
            if (addition.startsBeforeDisjoint(r)) {
                // insert before r
                iter.previous();
                iter.add(addition);
                return;
            }
            // if disjoint and after r, a future iteration will handle it
        }
        // ok, must be after last interval (and disjoint from last interval)
        // just add it
        intervals.add(addition);
    }

    /**
     * combine all sets in the array returned the or'd value
     */
    public static IntIntervalSet or(IntIntervalSet[] sets) {
        IntIntervalSet r = new IntIntervalSet();
        for (IntIntervalSet s : sets) r.addAll(s);
        return r;
    }

    @Override
    public IntIntervalSet addAll(IntSet set) {
        if (set == null) {
            return this;
        }

        if (set instanceof IntIntervalSet) {
            IntIntervalSet other = (IntIntervalSet) set;
            // walk set and add each interval
            int n = other.intervals.size();
            for (int i = 0; i < n; i++) {
                IntInterval I = other.intervals.get(i);
                this.add(I.a, I.b);
            }
        } else {
            for (int value : set.toList()) {
                add(value);
            }
        }

        return this;
    }

    public IntIntervalSet complement(int minElement, int maxElement) {
        return this.complement(IntIntervalSet.of(minElement, maxElement));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntIntervalSet complement(IntSet vocabulary) {
        if (vocabulary == null || vocabulary.isNil()) {
            return null; // nothing in common with null set
        }

        IntIntervalSet vocabularyIS;
        if (vocabulary instanceof IntIntervalSet) {
            vocabularyIS = (IntIntervalSet) vocabulary;
        } else {
            vocabularyIS = new IntIntervalSet();
            vocabularyIS.addAll(vocabulary);
        }

        return vocabularyIS.subtract(this);
    }

    @Override
    public IntIntervalSet subtract(IntSet a) {
        if (a == null || a.isNil()) {
            return new IntIntervalSet(this);
        }

        if (a instanceof IntIntervalSet) {
            return subtract(this, (IntIntervalSet) a);
        }

        IntIntervalSet other = new IntIntervalSet();
        other.addAll(a);
        return subtract(this, other);
    }

    /**
     * Compute the set difference between two interval sets. The specific
     * operation is {@code left - right}. If either of the input sets is
     * {@code null}, it is treated as though it was an empty set.
     */

    public static IntIntervalSet subtract(IntIntervalSet left, IntIntervalSet right) {
        if (left == null || left.isNil()) {
            return new IntIntervalSet();
        }

        IntIntervalSet result = new IntIntervalSet(left);
        if (right == null || right.isNil()) {
            // right set has no elements; just return the copy of the current set
            return result;
        }

        int resultI = 0;
        int rightI = 0;
        while (resultI < result.intervals.size() && rightI < right.intervals.size()) {
            IntInterval resultIntInterval = result.intervals.get(resultI);
            IntInterval rightIntInterval = right.intervals.get(rightI);

            // operation: (resultIntInterval - rightIntInterval) and update indexes

            if (rightIntInterval.b < resultIntInterval.a) {
                rightI++;
                continue;
            }

            if (rightIntInterval.a > resultIntInterval.b) {
                resultI++;
                continue;
            }

            IntInterval beforeCurrent = null;
            IntInterval afterCurrent = null;
            if (rightIntInterval.a > resultIntInterval.a) {
                beforeCurrent = new IntInterval(resultIntInterval.a, rightIntInterval.a - 1);
            }

            if (rightIntInterval.b < resultIntInterval.b) {
                afterCurrent = new IntInterval(rightIntInterval.b + 1, resultIntInterval.b);
            }

            if (beforeCurrent != null) {
                if (afterCurrent != null) {
                    // split the current interval into two
                    result.intervals.set(resultI, beforeCurrent);
                    result.intervals.add(resultI + 1, afterCurrent);
                    resultI++;
                    rightI++;
                    continue;
                } else {
                    // replace the current interval
                    result.intervals.set(resultI, beforeCurrent);
                    resultI++;
                    continue;
                }
            } else {
                if (afterCurrent != null) {
                    // replace the current interval
                    result.intervals.set(resultI, afterCurrent);
                    rightI++;
                    continue;
                } else {
                    // remove the current interval (thus no need to increment resultI)
                    result.intervals.remove(resultI);
                    continue;
                }
            }
        }

        // If rightI reached right.intervals.size(), no more intervals to subtract from result.
        // If resultI reached result.intervals.size(), we would be subtracting from an empty set.
        // Either way, we are done.
        return result;
    }

    @Override
    public IntIntervalSet or(IntSet a) {
        IntIntervalSet o = new IntIntervalSet();
        o.addAll(this);
        o.addAll(a);
        return o;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntIntervalSet and(IntSet other) {
        if (other == null) { //|| !(other instanceof IntIntervalSet) ) {
            return null; // nothing in common with null set
        }

        List<IntInterval> myIntIntervals = this.intervals;
        List<IntInterval> theirIntIntervals = ((IntIntervalSet) other).intervals;
        IntIntervalSet intersection = null;
        int mySize = myIntIntervals.size();
        int theirSize = theirIntIntervals.size();
        int i = 0;
        int j = 0;
        // iterate down both interval lists looking for nondisjoint intervals
        while (i < mySize && j < theirSize) {
            IntInterval mine = myIntIntervals.get(i);
            IntInterval theirs = theirIntIntervals.get(j);
            //System.out.println("mine="+mine+" and theirs="+theirs);
            if (mine.startsBeforeDisjoint(theirs)) {
                // move this iterator looking for interval that might overlap
                i++;
            } else if (theirs.startsBeforeDisjoint(mine)) {
                // move other iterator looking for interval that might overlap
                j++;
            } else if (mine.properlyContains(theirs)) {
                // overlap, add intersection, get next theirs
                if (intersection == null) {
                    intersection = new IntIntervalSet();
                }
                intersection.add(mine.intersection(theirs));
                j++;
            } else if (theirs.properlyContains(mine)) {
                // overlap, add intersection, get next mine
                if (intersection == null) {
                    intersection = new IntIntervalSet();
                }
                intersection.add(mine.intersection(theirs));
                i++;
            } else if (!mine.disjoint(theirs)) {
                // overlap, add intersection
                if (intersection == null) {
                    intersection = new IntIntervalSet();
                }
                intersection.add(mine.intersection(theirs));
                // Move the iterator of lower range [a..b], but not
                // the upper range as it may contain elements that will collide
                // with the next iterator. So, if mine=[0..115] and
                // theirs=[115..200], then intersection is 115 and move mine
                // but not theirs as theirs may collide with the next range
                // in thisIter.
                // move both iterators to next ranges
                if (mine.startsAfterNonDisjoint(theirs)) {
                    j++;
                } else if (theirs.startsAfterNonDisjoint(mine)) {
                    i++;
                }
            }
        }
        if (intersection == null) {
            return new IntIntervalSet();
        }
        return intersection;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean contains(int el) {
        int n = intervals.size();
        int l = 0;
        int r = n - 1;
        // Binary search for the element in the (sorted,
        // disjoint) array of intervals.
        while (l <= r) {
            int m = (l + r) / 2;
            IntInterval I = intervals.get(m);
            int a = I.a;
            int b = I.b;
            if (b < el) {
                l = m + 1;
            } else if (a > el) {
                r = m - 1;
            } else { // el >= a && el <= b
                return true;
            }
        }
        return false;
    }

    public boolean contains(int al, int bl) {
        int n = intervals.size();
        int l = 0;
        int r = n - 1;
        // Binary search for the element in the (sorted,
        // disjoint) array of intervals.
        while (l <= r) {
            int m = (l + r) / 2;
            IntInterval I = intervals.get(m);
            int a = I.a;
            int b = I.b;
            if (b < al) {
                l = m + 1;
            } else if (a > al) {
                r = m - 1;
            } else if (al >= a && bl <= b) { // el >= a && el <= b
                return true;
            } else {
                return false;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNil() {
        return intervals == null || intervals.isEmpty();
    }

    /**
     * Returns the maximum value contained in the set if not isNil().
     *
     * @return the maximum value contained in the set.
     * @throws RuntimeException if set is empty
     */
    public int getMaxElement() {
        if (isNil()) {
            throw new RuntimeException("set is empty");
        }
        IntInterval last = intervals.get(intervals.size() - 1);
        return last.b;
    }

    /**
     * Returns the minimum value contained in the set if not isNil().
     *
     * @return the minimum value contained in the set.
     * @throws RuntimeException if set is empty
     */
    public int getMinElement() {
        if (isNil()) {
            throw new RuntimeException("set is empty");
        }

        return intervals.get(0).a;
    }

    /**
     * Return a list of IntInterval objects.
     */
    public List<IntInterval> getIntIntervals() {
        return intervals;
    }

    @Override
    public int hashCode() {
        int hash = MurmurHash.initialize();
        for (IntInterval I : intervals) {
            hash = MurmurHash.update(hash, I.a);
            hash = MurmurHash.update(hash, I.b);
        }

        hash = MurmurHash.finish(hash, intervals.size() * 2);
        return hash;
    }

    /**
     * Are two IntIntervalSets equal?  Because all intervals are sorted
     * and disjoint, equals is a simple linear walk over both lists
     * to make sure they are the same.  IntInterval.equals() is used
     * by the List.equals() method to check the ranges.
     */
    @Override
    public boolean equals(Object obj) {
        if (obj == null || !(obj instanceof IntIntervalSet)) {
            return false;
        }
        IntIntervalSet other = (IntIntervalSet) obj;
        return this.intervals.equals(other.intervals);
    }

    @Override
    public String toString() {
        return toString(false);
    }

    public String toString(boolean elemAreChar) {
        StringBuilder buf = new StringBuilder();
        if (this.intervals == null || this.intervals.isEmpty()) {
            return "{}";
        }
        if (this.size() > 1) {
            buf.append("{");
        }
        Iterator<IntInterval> iter = this.intervals.iterator();
        while (iter.hasNext()) {
            IntInterval I = iter.next();
            int a = I.a;
            int b = I.b;
            if (a == b) {
                if (a == Token.EOF) buf.append("<EOF>");
                else if (elemAreChar) buf.append("'").appendCodePoint(a).append("'");
                else buf.append(a);
            } else {
                if (elemAreChar) buf.append("'").appendCodePoint(a).append("'..'").appendCodePoint(b).append("'");
                else buf.append(a).append("..").append(b);
            }
            if (iter.hasNext()) {
                buf.append(", ");
            }
        }
        if (this.size() > 1) {
            buf.append("}");
        }
        return buf.toString();
    }

    /**
     * @deprecated Use {@link #toString(Vocabulary)} instead.
     */
    @Deprecated
    public String toString(String[] tokenNames) {
        return toString(VocabularyImpl.fromTokenNames(tokenNames));
    }

    public String toString(Vocabulary vocabulary) {
        StringBuilder buf = new StringBuilder();
        if (this.intervals == null || this.intervals.isEmpty()) {
            return "{}";
        }
        if (this.size() > 1) {
            buf.append("{");
        }
        Iterator<IntInterval> iter = this.intervals.iterator();
        while (iter.hasNext()) {
            IntInterval I = iter.next();
            int a = I.a;
            int b = I.b;
            if (a == b) {
                buf.append(elementName(vocabulary, a));
            } else {
                for (int i = a; i <= b; i++) {
                    if (i > a) buf.append(", ");
                    buf.append(elementName(vocabulary, i));
                }
            }
            if (iter.hasNext()) {
                buf.append(", ");
            }
        }
        if (this.size() > 1) {
            buf.append("}");
        }
        return buf.toString();
    }

    /**
     * @deprecated Use {@link #elementName(Vocabulary, int)} instead.
     */
    @Deprecated
    protected String elementName(String[] tokenNames, int a) {
        return elementName(VocabularyImpl.fromTokenNames(tokenNames), a);
    }


    protected String elementName(Vocabulary vocabulary, int a) {
        if (a == Token.EOF) {
            return "<EOF>";
        } else if (a == Token.EPSILON) {
            return "<EPSILON>";
        } else {
            return vocabulary.getDisplayName(a);
        }
    }

    @Override
    public int size() {
        int n = 0;
        int numIntIntervals = intervals.size();
        if (numIntIntervals == 1) {
            IntInterval firstIntInterval = this.intervals.get(0);
            return firstIntInterval.b - firstIntInterval.a + 1;
        }
        for (int i = 0; i < numIntIntervals; i++) {
            IntInterval I = intervals.get(i);
            n += (I.b - I.a + 1);
        }
        return n;
    }

    public IntegerList toIntegerList() {
        IntegerList values = new IntegerList(size());
        int n = intervals.size();
        for (int i = 0; i < n; i++) {
            IntInterval I = intervals.get(i);
            int a = I.a;
            int b = I.b;
            for (int v = a; v <= b; v++) {
                values.add(v);
            }
        }
        return values;
    }

    @Override
    public List<Integer> toList() {
        List<Integer> values = new ArrayList<Integer>();
        int n = intervals.size();
        for (int i = 0; i < n; i++) {
            IntInterval I = intervals.get(i);
            int a = I.a;
            int b = I.b;
            for (int v = a; v <= b; v++) {
                values.add(v);
            }
        }
        return values;
    }

    public Set<Integer> toSet() {
        Set<Integer> s = new HashSet<Integer>();
        for (IntInterval I : intervals) {
            int a = I.a;
            int b = I.b;
            for (int v = a; v <= b; v++) {
                s.add(v);
            }
        }
        return s;
    }

    /**
     * Get the ith element of ordered set.  Used only by RandomPhrase so
     * don't bother to implement if you're not doing that for a new
     * ANTLR code gen target.
     */
    public int get(int i) {
        int n = intervals.size();
        int index = 0;
        for (int j = 0; j < n; j++) {
            IntInterval I = intervals.get(j);
            int a = I.a;
            int b = I.b;
            for (int v = a; v <= b; v++) {
                if (index == i) {
                    return v;
                }
                index++;
            }
        }
        return -1;
    }

    public int[] toArray() {
        return toIntegerList().toArray();
    }

    @Override
    public void remove(int el) {
        if (readonly) throw new IllegalStateException("can't alter readonly IntIntervalSet");
        int n = intervals.size();
        for (int i = 0; i < n; i++) {
            IntInterval I = intervals.get(i);
            int a = I.a;
            int b = I.b;
            if (el < a) {
                break; // list is sorted and el is before this interval; not here
            }
            // if whole interval x..x, rm
            if (el == a && el == b) {
                intervals.remove(i);
                break;
            }
            // if on left edge x..b, adjust left
            if (el == a) {
                I.a++;
                break;
            }
            // if on right edge a..x, adjust right
            if (el == b) {
                I.b--;
                break;
            }
            // if in middle a..x..b, split interval
            if (el > a && el < b) { // found in this interval
                int oldb = I.b;
                I.b = el - 1;      // [a..x-1]
                add(el + 1, oldb); // add [x+1..b]
            }
        }
    }

    public boolean isReadonly() {
        return readonly;
    }

    public void setReadonly(boolean readonly) {
        if (this.readonly && !readonly) throw new IllegalStateException("can't alter readonly IntIntervalSet");
        this.readonly = readonly;
    }
}
