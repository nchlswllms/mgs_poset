r"""
We show that the poset of equivalence classes of maximal green sequences for the D4 quiver is not a lattice, as claimed in arXiv:2007.12664.

The program takes about 45 minutes to run.
"""


# ****************************************************************************
#    Copyright (C) 2021 Nicholas Williams <nchlswllms@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  https://www.gnu.org/licenses/
# ****************************************************************************


Q=DiGraph({1:{2:'a'},2:{3:'b',4:'c'}})
PQ=Q.path_semigroup()

indecomposables = set()
for x in Q:
    indecomposable = PQ.I(CC,x)
    while not indecomposable.is_zero():
        indecomposables.add(indecomposable)
        
        # Taking AR translates of projectives sometimes gives errors, so we need the following
        
        try:
            indecomposable = indecomposable.AR_translate()
        except:
            break
            
projectives = set()
for x in Q:
    projectives.add(PQ.P(CC, x))
    
zero = PQ.representation(CC)


def remove(input_set, element):
    
    r"""
    Return the set ``input_set`` with ``element`` removed.
    
    INPUT:
    
    - ``input_set`` -- set; a set of representations.
    - ``element`` -- representation; the representation we wish to remove from ``input_set``.
    
    OUTPUT: set of representations
    
    EXAMPLES:
        sage: remove(indecomposables,PQ.P(CC,3))
        {Representation with dimension vector (0, 0, 0, 1),
         Representation with dimension vector (0, 1, 0, 0),
         Representation with dimension vector (0, 1, 0, 1),
         Representation with dimension vector (0, 1, 1, 0),
         Representation with dimension vector (0, 1, 1, 1),
         Representation with dimension vector (1, 0, 0, 0),
         Representation with dimension vector (1, 1, 0, 0),
         Representation with dimension vector (1, 1, 0, 1),
         Representation with dimension vector (1, 1, 1, 0),
         Representation with dimension vector (1, 1, 1, 1),
         Representation with dimension vector (1, 2, 1, 1)}
        
    NOTE::
        
        This is needed because the usual .remove() method does not seem to work for sets of representations.
        It might be related that Sage does not always recognise equal representations as equal. This is why we compare dimension vectors instead.
        
    """
    
    return {x for x in input_set if not x.dimension_vector() == element.dimension_vector()}


def complement(set1, set2):
    
    r"""
    Return the set ``set1`` with the elements of ``set2`` removed.
    
    INPUT:
    
    - ``set1`` -- set; a set of representations.
    - ``set2`` -- set; a set of representations.
    
    OUTPUT: set of representations
    
    EXAMPLES:
        sage: complement(indecomposables, projectives)
        {Representation with dimension vector (0, 1, 0, 0),
         Representation with dimension vector (0, 1, 0, 1),
         Representation with dimension vector (0, 1, 1, 0),
         Representation with dimension vector (1, 0, 0, 0),
         Representation with dimension vector (1, 1, 0, 0),
         Representation with dimension vector (1, 1, 0, 1),
         Representation with dimension vector (1, 1, 1, 0),
         Representation with dimension vector (1, 2, 1, 1)}
        
    NOTE::
        
        This is needed because using ``-`` does not seem to work for sets of representations.
        It might be related that Sage does not always recognise equal representations as equal. This is why we compare dimension vectors instead.
        
    """
    
    output = set1
    for y in set2:
        output = remove(output, y)
    
    return output

    
# It doesn't look possible to get summands from direct sums, so I am going to store decomposable modules as sets, and then 
# add them together when need be
            
def tau_rigid(M, P):
    
    r"""
    Return whether the pair (M, P) is tau-rigid.
    
    INPUT:
    
    - ``M`` -- set; a set of representations, taken to be the set of indecomposable summands of a module M.
    - ``P`` -- set; a set of representations, taken to be the set of indecomposable summands of a projective P.
    
    OUTPUT: Truth value
    
    EXAMPLES:
        sage: tau_rigid({PQ.P(CC,4)}, {zero})
        True
        sage: tau_rigid({PQ.P(CC,4)}, {PQ.P(CC,4)})
        False
        
    NOTE::
    
        We store decomposable modules as sets of their indecomposable summands to make mutation easier.
        
    """
    
    # M and P might be empty sets, so we need to raise exceptions when converting them to direct sums
    
    try:
        M = zero.direct_sum(M)
    except:
        M = zero
    try:
        P = zero.direct_sum(P)
    except:
        P = zero
    
    if not M.Hom(M.AR_translate()).dimension() == 0:
        return False
    
    if not P.Hom(M).dimension()==0:
        return False
    
    return True


def mutate(tau_tilting_pair,summand):
    
    r"""
    Mutate tau_tilting_pair at summand.
    
    INPUT:
    
    - ``tau_tilting_pair`` -- tuple; a pair of frozensets of representations, taken to be the two sets of summands of a support tau-tilting pair.
    - ``summand`` -- tuple; a pair of representations, one of which is assumed to be None. This is taken to be a summand of tau_tilting_pair one wishes to mutate at.
    
    OUTPUT: Pair of frozensets of representations.
    
    EXAMPLES:
        sage: mutate((projectives, set()), (PQ.P(CC,4), None))
        (frozenset({Representation with dimension vector (0, 0, 1, 0),
            Representation with dimension vector (0, 1, 1, 0),
            Representation with dimension vector (0, 1, 1, 1),
            Representation with dimension vector (1, 1, 1, 1)}),
         frozenset())
         sage: mutate((projectives, set()), (PQ.P(CC,3), None))
         (frozenset({Representation with dimension vector (0, 0, 0, 1),
            Representation with dimension vector (0, 1, 0, 1),
            Representation with dimension vector (0, 1, 1, 1),
            Representation with dimension vector (1, 1, 1, 1)}),
         frozenset())
         sage: mutate((projectives, set()), (PQ.P(CC,2), None))
         (frozenset({Representation with dimension vector (0, 0, 0, 1),
            Representation with dimension vector (0, 0, 1, 0),
            Representation with dimension vector (1, 0, 0, 0),
            Representation with dimension vector (1, 1, 1, 1)}),
         frozenset())
         sage: mutate((projectives, set()), (PQ.P(CC,1), None))
         (frozenset({Representation with dimension vector (0, 0, 0, 1),
            Representation with dimension vector (0, 0, 1, 0),
            Representation with dimension vector (0, 1, 1, 1)}),
         frozenset({Representation with dimension vector (1, 1, 1, 1)}))
           
    NOTE::
    
        The output is a frozenset so that one can store a set of support tau-tilting pairs.
        If both m and p are not None, then the function mutates at m.
        This function uses the most naive way of computing a mutation: checking every other indecomposable to find something tau-rigid.
        One could probably find a faster function by computing approximations, but that is more difficult to do.
        
    """
    
    M, P = tau_tilting_pair
    m, p = summand
    
    if not m is None:
        
        if not m in M: # We do nothing if m is not actually a summand of M
            return (M, P)
        
        for module in complement(indecomposables, M):
            
            if tau_rigid(frozenset(remove(set(M), m).union({module})),frozenset(P)):
                return (frozenset(remove(set(M), m).union({module})),frozenset(P))
            
        # If we cannot replace m in M, then we look to replace it with a shifted projective
        
        for projective in complement(projectives,P):
            
            if tau_rigid(frozenset(remove(set(M), m)),frozenset(set(P).union({projective}))):
                return (frozenset(remove(set(M), m)),frozenset(set(P).union({projective}))) 
    
    if not p is None:
        
        if not p in P: # We do nothing if p is not actually a summand of P
            return (M,P)
            
        for module in complement(indecomposables, M):
            
            if tau_rigid(frozenset(set(M).union({module})),frozenset(remove(set(P),p))):
                return (frozenset(set(M).union({module})),frozenset(remove(set(P),p)))
            
    return (M,P)


def order(ttp1,ttp2):
    
    r"""
    Checks whether ttp1 <= ttp2 in the order on support tau-tilting pairs from Adachi--Iyama--Reiten
    
    INPUT:
    
    - ``ttp1`` -- tuple; a pair of frozensets of representations, taken to be the two sets of summands of a support tau-tilting pair.
    - ``ttp2`` -- tuple; a pair of frozensets of representations, taken to be the two sets of summands of a support tau-tilting pair.
    
    OUTPUT: Truth value
    
    EXAMPLES:
        sage: order((frozenset(), projectives), (projectives, frozenset()))
        True
        sage: order((projectives, frozenset()), (frozenset(), projectives))
        False
        
    """
    
    M1, P1 = ttp1
    M2, P2 = ttp2
    
    try:
        M1 = zero.direct_sum(M1)
    except:
        M1 = zero
    try:
        M2 = zero.direct_sum(M2)
    except:
        M2 = zero
    
    if M1.Hom(M2.AR_translate()).dimension() == 0 and P2.issubset(P1):
        return True
    
    return False


def decreasing_mutations(tau_tilting_pair):
    
    r"""
    Returns the set of mutations of the support tau-tilting pair which are decreasing with respect to the order.
    
    INPUT:
    
    - ``tau_tilting_pair`` -- tuple; a pair of frozensets of representations, taken to be the two sets of summands of a support tau-tilting pair.
    
    OUTPUT: Set
    
    EXAMPLES:
        sage: decreasing_mutations((projectives, frozenset()))
        {(frozenset({Representation with dimension vector (0, 0, 0, 1),
             Representation with dimension vector (0, 0, 1, 0),
             Representation with dimension vector (0, 1, 1, 1)}),
          frozenset({Representation with dimension vector (1, 1, 1, 1)})),
         (frozenset({Representation with dimension vector (0, 0, 0, 1),
             Representation with dimension vector (0, 0, 1, 0),
             Representation with dimension vector (1, 0, 0, 0),
             Representation with dimension vector (1, 1, 1, 1)}),
          frozenset()),
         (frozenset({Representation with dimension vector (0, 0, 0, 1),
             Representation with dimension vector (0, 1, 0, 1),
             Representation with dimension vector (0, 1, 1, 1),
             Representation with dimension vector (1, 1, 1, 1)}),
          frozenset()),
         (frozenset({Representation with dimension vector (0, 0, 1, 0),
             Representation with dimension vector (0, 1, 1, 0),
             Representation with dimension vector (0, 1, 1, 1),
             Representation with dimension vector (1, 1, 1, 1)}),
          frozenset())}
        sage: decreasing_mutations((frozenset(), projectives))
        set()
        
    """
    
    M,P = tau_tilting_pair
    
    dec_muts = set()
    
    for m in M: # Only mutation at summands of M can be decreasing
        
        mutation = mutate(tau_tilting_pair,(m,None))
        
        if order(mutation,tau_tilting_pair):
            dec_muts.add(mutation)
            
    return dec_muts


def tau_tilt_dict():
    
    r"""
    Return a dictionary which maps a support tau-tilting pair to a list of its decreasing mutations.
    
    INPUT:
    
    OUTPUT: Dictionary
    
    EXAMPLES:
        sage: tau_tilt_dict()
        {(frozenset({Representation with dimension vector (0, 0, 0, 1),
             Representation with dimension vector (0, 0, 1, 0),
             Representation with dimension vector (0, 1, 1, 1),
             Representation with dimension vector (1, 1, 1, 1)}),
          frozenset()): [(frozenset({Representation with dimension vector (0, 0, 0, 1),
              Representation with dimension vector (0, 0, 1, 0),
              Representation with dimension vector (0, 1, 1, 1)}),
           frozenset({Representation with dimension vector (1, 1, 1, 1)})),
          (frozenset({Representation with dimension vector (0, 0, 0, 1),
              Representation with dimension vector (0, 0, 1, 0),
              Representation with dimension vector (1, 0, 0, 0),
              Representation with dimension vector (1, 1, 1, 1)}),
           frozenset()),
          (frozenset({Representation with dimension vector (0, 0, 0, 1),
              Representation with dimension vector (0, 1, 0, 1),
              Representation with dimension vector (0, 1, 1, 1),
              Representation with dimension vector (1, 1, 1, 1)}),
           frozenset()),
          (frozenset({Representation with dimension vector (0, 0, 1, 0),
              Representation with dimension vector (0, 1, 1, 0),
              Representation with dimension vector (0, 1, 1, 1),
              Representation with dimension vector (1, 1, 1, 1)}),
           frozenset())],
           ...
           ...
         (frozenset({Representation with dimension vector (0, 1, 0, 0),
             Representation with dimension vector (1, 1, 0, 0)}),
          frozenset({Representation with dimension vector (0, 0, 0, 1),
             Representation with dimension vector (0, 0, 1, 0)})): [(frozenset({Representation with dimension vector (1, 0, 0, 0),
              Representation with dimension vector (1, 1, 0, 0)}),
           frozenset({Representation with dimension vector (0, 0, 0, 1),
              Representation with dimension vector (0, 0, 1, 0)})),
          (frozenset({Representation with dimension vector (0, 1, 0, 0)}),
           frozenset({Representation with dimension vector (0, 0, 0, 1),
              Representation with dimension vector (0, 0, 1, 0),
              Representation with dimension vector (1, 1, 1, 1)}))]}
        
    NOTE::
    
        This function is slow. It takes about half an hour to run for D4
        
    """
    
    pairs = [(frozenset(projectives),frozenset())]
    dictionary = {}
    
    counter = 0
    
    while counter < len(pairs):
        
        dec_muts = list(decreasing_mutations(pairs[counter]))
        dictionary[pairs[counter]] = dec_muts
        
        for x in dec_muts:
            
            if x not in set(pairs):
                pairs.append(x)
        
        counter += 1
        
    return dictionary


def tau_tilt_poset():
    
    r"""
    Returns the poset of support tau-tilting pairs.
    
    INPUT:
    
    OUTPUT: sage poset object
    
    EXAMPLES:
        sage: tau_tilt_poset()
        Finite poset containing 50 elements (use the .plot() method to plot)
        
    """
    
    return Poset(tau_tilt_dict())


def mgs_summands():
    
    r"""
    Returns a set which contains the frozensets of summands of maximal green sequences (apart from shifted projectives).
    
    INPUT:
    
    OUTPUT: Set
    
    EXAMPLES:
        sage: mgs_summands()
        {frozenset({Representation with dimension vector (0, 0, 0, 1),
            Representation with dimension vector (0, 0, 1, 0),
            Representation with dimension vector (0, 1, 1, 1),
            Representation with dimension vector (1, 1, 1, 1)}),
         ...
         ...
         frozenset({Representation with dimension vector (0, 0, 0, 1),
            Representation with dimension vector (0, 0, 1, 0),
            Representation with dimension vector (0, 1, 0, 0),
            Representation with dimension vector (0, 1, 0, 1),
            Representation with dimension vector (0, 1, 1, 0),
            Representation with dimension vector (0, 1, 1, 1),
            Representation with dimension vector (1, 0, 0, 0),
            Representation with dimension vector (1, 1, 0, 0),
            Representation with dimension vector (1, 1, 0, 1),
            Representation with dimension vector (1, 1, 1, 0),
            Representation with dimension vector (1, 1, 1, 1),
            Representation with dimension vector (1, 2, 1, 1)})}
        
    NOTE::
    
        For any maximal green sequence G, mgs_summands() contains the frozenset of summands of G, excluding the shifted projectives.
        
    """
    
    chain_set = set()
    
    for chain in tau_tilt_poset().maximal_chains():
        
        equiv_class = set()
        
        for pair in chain:
            
            M,P = pair
            
            for m in M: # We only need the summands of M, since the summands of P are in every maximal green sequence
                
                equiv_class.add(m)
        
        chain_set.add(frozenset(equiv_class))
        
    return chain_set


def contained(set1,set2):
    
    r"""
    Returns whether set1 is a subset of set2.
    
    INPUT:
    
    - ``set1`` -- set;
    - ``set2`` -- set;
    
    OUTPUT: Truth value
    
    EXAMPLES:
        sage: contained({1, 2}, {1, 2, 3})
        True
        sage: contained({1, 2, 3}, {1, 2})
        False
        
    NOTE::
    
        This is needed so that we can call the function when we define the poset of equivalence classes of maximal green sequences.
        
    """
    
    return set1.issubset(set2)


def mgs_poset():
    
    r"""
    Returns the poset of equivalence classes of maximal green sequences.
    
    INPUT:
    
    OUTPUT: sage poset object
    
    EXAMPLES:
        sage: mgs_poset()
        Finite poset containing 48 elements (use the .plot() method to plot)
        
    """
    
    return Poset((mgs_summands(),contained))


mgs_poset().is_lattice() # This gives False, thus establishing our claim
