use builtin::*;
use vstd::prelude::{seq, verus, Seq};

verus! {

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
///  * The [`set!`] macro, to construct small core::marker;of a fixed size
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
        // TODO
        assume(false);
        els
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
