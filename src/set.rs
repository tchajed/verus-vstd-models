use builtin::*;
use vstd::prelude::{seq, verus, Seq};

verus! {

pub closed spec fn remove_duplicates<A>(l: Seq<A>) -> (lu: Seq<A>)
    decreases l.len(),
{
    if l.len() == 0 {
        seq![]
    } else {
        let a = l[0];
        seq![a] + remove_duplicates(l.skip(1).filter(|x| x != a))
    }
}

pub proof fn seq_cons_contains<A>(a: A, l: Seq<A>)
    ensures
        forall|x: A|
            #[trigger]
            (seq![a] + l).contains(x) <==> x == a || #[trigger]
            l.contains(x),
{
    assert forall|x: A| #[trigger] (seq![a] + l).contains(x) implies x == a || l.contains(x) by {}
    assert forall|x: A| x == a || l.contains(x) implies #[trigger]
    (seq![a] + l).contains(x) by {
        if x == a {
            assert((seq![a] + l)[0] == x);
        } else {
            let i = choose|i: int| 0 <= i < l.len() && l[i] == x;
            assert((seq![a] + l)[i + 1] == x);
        }
    }
}

pub proof fn seq_cons_contains_auto<A>()
    ensures
        forall|a: A, x: A, l: Seq<A>|
            #[trigger]
            (seq![a] + l).contains(x) <==> x == a || #[trigger]
            l.contains(x),
{
    assert forall|a: A, x: A, l: Seq<A>|
        #[trigger]
        (seq![a] + l).contains(x) <==> x == a || #[trigger]
        l.contains(x) by {
        seq_cons_contains(a, l);
    }
}

pub proof fn seq_cons_no_duplicates<A>(a: A, l: Seq<A>)
    requires
        l.no_duplicates(),
        !l.contains(a),
    ensures
        (seq![a] + l).no_duplicates(),
{
}

pub proof fn seq_push_no_duplicates<A>(l: Seq<A>, a: A)
    requires
        l.no_duplicates(),
        !l.contains(a),
    ensures
        l.push(a).no_duplicates(),
{
}

pub proof fn remove_duplicates_spec<A>(l: Seq<A>)
    ensures
        forall|x: A| #[trigger] l.contains(x) <==> remove_duplicates(l).contains(x),
        remove_duplicates(l).no_duplicates(),
    decreases l.len(),
{
    if l.len() == 0 {
        return ;
    } else {
        let a = l[0];
        let pred = |x: A| x != a;
        remove_duplicates_spec(l.skip(1).filter(pred));
        seq_cons_contains_auto::<A>();
        assert forall|x: A| l.skip(1).filter(pred).contains(x) implies #[trigger]
        l.contains(x) by {}
        assert forall|x: A| #[trigger] l.contains(x) implies l.skip(1).filter(pred).contains(x) || x
            == a by {
            if x != a {
                assert(pred(x));
                let i = choose|i: int| 0 <= i < l.len() && l[i] == x;
                assert(i > 0);
                assert(l.skip(1)[i - 1] == x);
                assert(l.skip(1).contains(x));
            }
        }
        assert forall|x: A| remove_duplicates(l).contains(x) implies #[trigger]
        l.contains(x) by {}
        assert(remove_duplicates(l).no_duplicates()) by {
            if remove_duplicates(l.skip(1).filter(pred)).contains(a) {
                assert(l.skip(1).filter(pred).contains(a));
                assert(false);
            }
            seq_cons_no_duplicates(a, remove_duplicates(l.skip(1).filter(pred)));
        }
        return ;
    }
}

pub proof fn seq_push_contains<A>()
    ensures
        forall|s: Seq<A>, a: A, x: A| s.push(a).contains(x) <==> s.contains(x) || x == a,
{
    assert forall|s: Seq<A>, a: A, x: A| s.push(a).contains(x) <==> s.contains(x) || x == a by {
        assert(s.push(a)[s.len() as int] == a);
        if x == a {
            assert(s.push(a).contains(x));
        } else if s.contains(x) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
            assert(s.push(a)[i] == x);
        } else {
            if s.push(a).contains(x) {
                let i = choose|i: int| 0 <= i < s.push(a).len() && s.push(a)[i] == x;
                assert(s[i] == x);
            }
        }
    }
}

proof fn lemma_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger]
        s.subrange(j, k).len() == k - j,
{
}

pub proof fn seq_drop_last_contains<A>(s: Seq<A>)
    requires
        s.len() >= 1,
    ensures
        forall|x: A|
            (#[trigger]
            s.drop_last().contains(x) || x == s.last()) <==> s.contains(x),
{
    assert forall|x: A| s.len() >= 1 implies (#[trigger]
    s.drop_last().contains(x) || x == s.last()) <==> s.contains(x) by {
        if s.len() >= 1 {
            lemma_seq_subrange_len(s, 0, s.len() as int - 1);
            assert(s.drop_last().len() == s.len() as int - 1);
            if x == s.last() {
                assert(s[s.len() - 1] == x);
                assert(s.contains(x));
            } else if s.drop_last().contains(x) {
                let i = choose|i: int| 0 <= i < s.drop_last().len() && s.drop_last()[i] == x;
                assert(i < s.len());
                assert(s[i] == x);
                assert(s.contains(x));
            } else if s.contains(x) {
                let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
                if x != s.last() {
                    assert(s.drop_last()[i] == x);
                }
            }
        }
    }
}

closed spec fn remove1<A>(s: Seq<A>, a: A) -> Seq<A>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        let (s2, x) = (s.drop_last(), s.last());
        if x == a {
            s2
        } else {
            remove1(s2, a).push(x)
        }
    }
}

proof fn remove1_spec<A>(s: Seq<A>, a: A)
    requires
        s.contains(a),
        s.no_duplicates(),
    ensures
        ({
            let r = remove1(s, a);
            &&& forall|x: A| r.contains(x) <==> (s.contains(x) && x != a)
            &&& !r.contains(a)
            &&& r.no_duplicates()
            &&& r.len() + 1 == s.len()
        }),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(false);
        return ;
    }
    let r = remove1(s, a);
    if s.last() == a {
        assert forall|x: A| r.contains(x) implies (s.contains(x) && x != a) by {}
        assert forall|x: A| (s.contains(x) && x != a) implies r.contains(x) by {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
            assert(s.drop_last()[i] == x);
        }
        return ;
    } else {
        assert(s.drop_last().no_duplicates());
        seq_push_contains::<A>();
        let i = choose|i: int| 0 <= i < s.len() && s[i] == a;
        assert(s.drop_last()[i] == a);
        remove1_spec(s.drop_last(), a);
        assert(r == remove1(s.drop_last(), a).push(s.last()));
        seq_drop_last_contains(s.drop_last());
        assert forall|x: A| r.contains(x) implies (s.contains(x) && x != a) by {}
        assert forall|x: A| (s.contains(x) && x != a) implies r.contains(x) by {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
            assert(s.drop_last().push(s.last())[i] == x);
        }
        seq_push_no_duplicates(remove1(s.drop_last(), a), s.last());
        return ;
    }
}

/// `Set<A>` is a set type for specifications.
///
/// An object `set: Set<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
///
/// In general, a set might be infinite.
/// To work specifically with finite sets, see the [`self.finite()`](Set::finite) predicate.
///
/// Sets can be constructed in a few different ways:
///  * [`Set::empty`] gives an empty set
///  * [`Set::full`] gives the set of all elements in `A`
///  * [`Set::new`] constructs a set from a boolean predicate
///  * The [`set!`] macro, to construct small sets of a fixed size
///  * By manipulating an existing sequence with [`Set::union`], [`Set::intersect`],
///    [`Set::difference`], [`Set::complement`], [`Set::filter`], [`Set::insert`],
///    or [`Set::remove`].
///
/// To prove that two sequences are equal, it is usually easiest to use the extensionality
/// operator `=~=`.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct Set<A> {
    has: spec_fn(A) -> bool,
}

impl<A> Set<A> {
    /// The "empty" set.
    pub closed spec fn empty() -> Set<A> {
        Set { has: |a| false }
    }

    /// Set whose membership is determined by the given boolean predicate.
    pub closed spec fn new(f: spec_fn(A) -> bool) -> Set<A> {
        Set { has: f }
    }

    /// The "full" set, i.e., set containing every element of type `A`.
    pub open spec fn full() -> Set<A> {
        Self::new(|a| true)
    }

    /// Predicate indicating if the set contains the given element.
    pub closed spec fn contains(self, a: A) -> bool {
        (self.has)(a)
    }

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns `true` if for every value `a: A`, it is either in both input sets or neither.
    /// This is equivalent to the sets being actually equal
    /// by [`axiom_set_ext_equal`].
    ///
    /// To prove that two sets are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_sets_equal!`](crate::set_lib::assert_sets_equal) macro,
    /// rather than using `.ext_equal` directly.
    #[deprecated = "use =~= or =~~= instead"]
    pub open spec fn ext_equal(self, s2: Set<A>) -> bool {
        self =~= s2
    }

    /// Returns `true` if the first argument is a subset of the second.
    pub open spec fn subset_of(self, s2: Set<A>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
    }

    #[verifier(inline)]
    pub open spec fn spec_le(self, s2: Set<A>) -> bool {
        self.subset_of(s2)
    }

    /// Returns a new set with the given element inserted.
    /// If that element is already in the set, then an identical set is returned.
    pub closed spec fn insert(self, a: A) -> Set<A> {
        Set::new(|x| self.contains(x) || x == a)
    }

    /// Returns a new set with the given element removed.
    /// If that element is already absent from the set, then an identical set is returned.
    pub closed spec fn remove(self, a: A) -> Set<A> {
        Set::new(|x| self.contains(x) && x != a)
    }

    /// Union of two sets.
    pub closed spec fn union(self, s2: Set<A>) -> Set<A> {
        Set::new(|x| self.contains(x) || s2.contains(x))
    }

    /// `+` operator, synonymous with `union`
    #[verifier(inline)]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// Intersection of two sets.
    pub closed spec fn intersect(self, s2: Set<A>) -> Set<A> {
        Set::new(|x| self.contains(x) && s2.contains(x))
    }

    /// `*` operator, synonymous with `intersect`
    #[verifier(inline)]
    pub open spec fn spec_mul(self, s2: Set<A>) -> Set<A> {
        self.intersect(s2)
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    pub closed spec fn difference(self, s2: Set<A>) -> Set<A> {
        Set::new(|x| self.contains(x) && !s2.contains(x))
    }

    /// Set complement (within the space of all possible elements in `A`).
    /// `-` operator, synonymous with `difference`
    #[verifier(inline)]
    pub open spec fn spec_sub(self, s2: Set<A>) -> Set<A> {
        self.difference(s2)
    }

    pub closed spec fn complement(self) -> Set<A> {
        Set::new(|x| !self.contains(x))
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    pub open spec fn filter(self, f: spec_fn(A) -> bool) -> Set<A> {
        self.intersect(Self::new(f))
    }

    /// Returns `true` is the elements of the set are covered by `els` (for proving finiteness).
    spec fn has_els(self, els: Seq<A>) -> bool {
        forall|x: A| #[trigger] self.contains(x) ==> els.contains(x)
    }

    spec fn has_els_exact(self, els: Seq<A>) -> bool {
        &&& forall|x: A| #[trigger] self.contains(x) <==> els.contains(x)
        &&& els.no_duplicates()
    }

    proof fn has_els_to_exact(self, els: Seq<A>) -> (uels: Seq<A>)
        requires
            self.has_els(els),
        ensures
            self.has_els_exact(uels),
    {
        // let pred = |x| self.contains(x);
        let uels = els.filter(|x| self.contains(x));
        els.filter_lemma(|x| self.contains(x));
        assert forall|x: A| self.contains(x) implies uels.contains(x) by {
            // NOTE: this did not work, needed els.filter_lemma
            // assert(els.contains(x));
            // let i = choose|i: int| 0 <= i < els.len() && els[i] == x;
            // assert(pred(x));
            // assert(els.filter(pred).contains(els[i]));
        }
        assert forall|x: A| uels.contains(x) implies self.contains(x) by {}
        let uels = remove_duplicates(uels);
        remove_duplicates_spec(els.filter(|x| self.contains(x)));
        assert(uels.no_duplicates());
        assert forall|x: A| self.contains(x) <==> uels.contains(x) by {}
        uels
    }

    /// Returns `true` if the set is finite.
    pub closed spec fn finite(self) -> bool {
        exists|els: Seq<A>| self.has_els(els)
    }

    /// Cardinality of the set. (Only meaningful if a set is finite.)
    pub closed spec fn len(self) -> nat {
        let els = choose|els: Seq<A>| self.has_els_exact(els);
        els.len()
    }

    /// Chooses an arbitrary element of the set.
    ///
    /// This is often useful for proofs by induction.
    ///
    /// (Note that, although the result is arbitrary, it is still a _deterministic_ function
    /// like any other `spec` function.)
    pub open spec fn choose(self) -> A {
        choose|a: A| self.contains(a)
    }

    /// Returns `true` if the sets are disjoint, i.e., if their intersection is
    /// the empty set.
    pub open spec fn disjoint(self, s2: Self) -> bool {
        forall|a: A| self.contains(a) ==> !s2.contains(a)
    }
}

// Trusted axioms
pub proof fn lemma_set_empty<A>(a: A)
    ensures
        !(#[trigger]
        Set::empty().contains(a)),
{
}

/// The empty set contains no elements
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_empty<A>(a: A)
    ensures
        !(#[trigger]
        Set::empty().contains(a)),
{
}

pub proof fn lemma_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        Set::new(f).contains(a) == f(a),
{
}

/// A call to `Set::new` with the predicate `f` contains `a` if and only if `f(a)` is true.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        Set::new(f).contains(a) == f(a),
{
}

pub proof fn lemma_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger]
        s.insert(a).contains(a),
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger]
        s.insert(a).contains(a),
{
}

pub proof fn lemma_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.insert(a2).contains(a1) == s.contains(a1),
{
}

pub proof fn lemma_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger]
        s.remove(a).contains(a)),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger]
        s.remove(a).contains(a)),
{
}

pub proof fn lemma_set_remove_insert<A>(s: Set<A>, a: A)
    requires
        s.contains(a),
    ensures
        (#[trigger]
        s.remove(a)).insert(a) == s,
{
    lemma_set_ext_equal(s.remove(a).insert(a), s);
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_insert<A>(s: Set<A>, a: A)
    requires
        s.contains(a),
    ensures
        (#[trigger]
        s.remove(a)).insert(a) == s,
{
}

pub proof fn lemma_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.remove(a2).contains(a1) == s.contains(a1),
{
}

pub proof fn lemma_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

pub proof fn lemma_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

pub proof fn lemma_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

pub proof fn lemma_set_complement<A>(s: Set<A>, a: A)
    ensures
        s.complement().contains(a) == !s.contains(a),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_complement<A>(s: Set<A>, a: A)
    ensures
        s.complement().contains(a) == !s.contains(a),
{
}

pub proof fn lemma_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger]
        (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a)),
{
    if forall|a: A| s1.contains(a) == s2.contains(a) {
        assert forall|a: A| #[trigger] (s1.has)(a) == (s2.has)(a) by {
            assert((s1.has)(a) == s1.contains(a));
        }
    }
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger]
        (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a)),
{
}

pub proof fn lemma_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger]
        (s1 =~~= s2) <==> s1 =~= s2,
{
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger]
        (s1 =~~= s2) <==> s1 =~= s2,
{
}

pub proof fn lemma_set_empty_finite<A>()
    ensures
        #[trigger]
        Set::<A>::empty().finite(),
{
    assert(Set::<A>::empty().has_els(seq![]));
}

// Trusted axioms about finite
/// The empty set is finite.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_finite<A>()
    ensures
        #[trigger]
        Set::<A>::empty().finite(),
{
}

pub proof fn lemma_set_insert_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger]
        s.insert(a).finite(),
{
    let els = choose|els: Seq<A>| s.has_els(els);
    assert forall|x: A| s.insert(a).contains(x) implies els.push(a).contains(x) by {
        if s.contains(x) {
            let i = choose|i: int| 0 <= i < els.len() && els[i] == x;
            assert(els.push(a)[i] == x);
        } else {
            assert(x == a);
            assert(els.push(a)[els.len() as int] == a);
            assert(els.push(a).contains(a));
        }
    }
    assert(s.insert(a).has_els(els.push(a)));
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger]
        s.insert(a).finite(),
{
}

pub proof fn lemma_set_remove_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger]
        s.remove(a).finite(),
{
    let els = choose|els: Seq<A>| s.has_els(els);
    // els is an over-approximation
    assert(s.remove(a).has_els(els));
}

/// The result of removing an element `a` from a finite set `s` is also finite.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger]
        s.remove(a).finite(),
{
}

pub proof fn lemma_set_union_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger]
        s1.union(s2).finite(),
{
    let els1 = choose|els: Seq<A>| s1.has_els(els);
    let els2 = choose|els: Seq<A>| s2.has_els(els);
    assert forall|x: A| s1.union(s2).contains(x) implies (els1 + els2).contains(x) by {
        if s1.contains(x) {
            let i = choose|i: int| 0 <= i < els1.len() && els1[i] == x;
            assert((els1 + els2)[i] == x);
        } else {
            assert(s2.contains(x));
            let i = choose|i: int| 0 <= i < els2.len() && els2[i] == x;
            assert((els1 + els2)[els1.len() + i] == x);
        }
    }
    assert(s1.union(s2).has_els(els1 + els2));
}

/// The union of two finite sets is finite.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_union_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger]
        s1.union(s2).finite(),
{
}

pub proof fn lemma_set_intersect_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger]
        s1.intersect(s2).finite(),
{
    if s1.finite() {
        let els = choose|els: Seq<A>| s1.has_els(els);
        assert(s1.intersect(s2).has_els(els));
    } else {
        assert(s2.finite());
        let els = choose|els: Seq<A>| s2.has_els(els);
        assert(s1.intersect(s2).has_els(els));
    }
}

/// The intersection of two finite sets is finite.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger]
        s1.intersect(s2).finite(),
{
}

pub proof fn lemma_set_difference_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        #[trigger]
        s1.difference(s2).finite(),
{
    let els = choose|els: Seq<A>| s1.has_els(els);
    assert(s1.difference(s2).has_els(els));
}

/// The set difference between two finite sets is finite.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_difference_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        #[trigger]
        s1.difference(s2).finite(),
{
}

pub proof fn lemma_set_choose_finite<A>(s: Set<A>)
    requires
        !s.finite(),
    ensures
        #[trigger]
        s.contains(s.choose()),
{
    // we just need to prove s is non-empty, and if it were empty its elements would be the empty
    // sequence and it would be finite
    assert(!s.has_els(seq![]));
}

/// An infinite set `s` contains the element `s.choose()`.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_choose_finite<A>(s: Set<A>)
    requires
        !s.finite(),
    ensures
        #[trigger]
        s.contains(s.choose()),
{
}

pub proof fn lemma_set_empty_len<A>()
    ensures
        #[trigger]
        Set::<A>::empty().len() == 0,
{
    assert(Set::<A>::empty().has_els_exact(seq![]));  // witness for choose
    let els = choose|els: Seq<A>| Set::<A>::empty().has_els_exact(els);
    if els.len() > 0 {
        assert(Set::<A>::empty().contains(els[0]));
    }
    assert(els.len() == 0);
}

// Trusted axioms about len
// Note: we could add more axioms about len, but they would be incomplete.
// The following, with axiom_set_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_len<A>()
    ensures
        #[trigger]
        Set::<A>::empty().len() == 0,
{
}

proof fn lemma_len_unique2<A>(s: Set<A>, els1: Seq<A>, els2: Seq<A>)
    requires
        s.has_els_exact(els1),
        s.has_els_exact(els2),
    ensures
        els1.len() == els2.len(),
    decreases els1.len()
{
    if els1.len() == 0 {
        if els2.len() != 0 {
            assert(s.contains(els2.first()));
            assert(false);
        }
        return;
    }
    let els1_next = els1.drop_last();
    let a = els1.last();
    let s_next = s.remove(a);
    let els2_next = remove1(els2, a);
    assert(els2.contains(a)) by {
        assert(els1.contains(a));
        assert(s.contains(a));
    }
    remove1_spec(els2, a);
    seq_drop_last_contains(els1);
    lemma_len_unique2(s.remove(a), els1_next, els2_next);
}

proof fn lemma_len_unique<A>(s: Set<A>, els: Seq<A>)
    requires
        s.has_els_exact(els),
    ensures
        s.len() == els.len(),
    decreases els.len()
{
    let els2 = choose|els_len: Seq<A>| #[trigger] s.has_els_exact(els_len) && els_len.len() == s.len();
    lemma_len_unique2(s, els, els2);
}

pub proof fn lemma_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger]
        s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),
{
    let els = choose|els: Seq<A>| s.has_els(els);
    let els = s.has_els_to_exact(els);
    lemma_len_unique(s, els);
    assert(s.len() == els.len());
    if s.contains(a) {
        assert(s.insert(a) =~= s);
        return ;
    } else {
        lemma_set_insert_finite(s, a);
        assert(els.push(a).no_duplicates());
        assert forall|x: A| s.insert(a).contains(x) implies els.push(a).contains(x) by {
            if x == a {
                assert(els.push(a)[els.len() as int] == a);
            } else {
                assert(s.contains(x));
                let i = choose|i: int| 0 <= i < s.len() && els[i] == x;
                assert(els.push(a)[i] == x);
            }
        }
        assert forall|x: A| els.push(a).contains(x) implies s.insert(a).contains(x) by {}
        assert(s.insert(a).has_els_exact(els.push(a)));
        lemma_len_unique(s.insert(a), els.push(a));
        return ;
    }
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger]
        s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),
{
}

pub proof fn lemma_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger]
        s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    if !s.contains(a) {
        assert(s.remove(a) =~= s);
        return ;
    } else {
        assert(s.remove(a).insert(a) =~= s);
        lemma_set_remove_finite(s, a);
        lemma_set_insert_len(s.remove(a), a);
        return ;
    }
}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger]
        s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
}

proof fn lemma_len_zero<A>(s: Set<A>)
    requires
        s.finite(),
        s.len() == 0,
    ensures
        s == Set::<A>::empty(),
{
    let els = choose|els: Seq<A>| s.has_els(els);
    let els = s.has_els_to_exact(els);
    lemma_len_unique(s, els);
    assert(els =~= seq![]);
    lemma_set_ext_equal(s, Set::<A>::empty());
}

pub proof fn lemma_set_contains_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
        #[trigger]
        s.contains(a),
    ensures
        #[trigger]
        s.len() != 0,
{
    if s.len() == 0 {
        lemma_len_zero(s);
    }
}

/// If a finite set `s` contains any element, it has length greater than 0.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_contains_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
        #[trigger]
        s.contains(a),
    ensures
        #[trigger]
        s.len() != 0,
{
}

pub proof fn lemma_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger]
        s.len() != 0,
    ensures
        #[trigger]
        s.contains(s.choose()),
{
    if forall|x: A| !s.contains(x) {
        lemma_set_empty_len::<A>();
        lemma_set_ext_equal(s, Set::<A>::empty());
        assert(false);
    }
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger]
        s.len() != 0,
    ensures
        #[trigger]
        s.contains(s.choose()),
{
}

} // verus!
