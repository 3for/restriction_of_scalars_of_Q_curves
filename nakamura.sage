load('fields.sage')
# this initializes a vector data with all the imaginary quadratic fields with class group C2 x C2 which are non-exceptional
load('non_abelian_extensions.sage')
# this initializes a dictionary non_abelian_extensions that contains, for each discriminant D a polynomial of degree 16 that generates a number field k, with the properties that:
# 1) k/Q is Galois 
# 2) k is a quadratic extension of the Hilbert class field H of K
# 3) The extension k/M is non-abelian
# these fields have been precomputed, but we check in the code below that they satisfy the three properties above

# uses magma_free to check whether the field K (a relative extension) is abelian or not
# this is used because the magma version that I have in my computer is a bit old, and it returns an error when calculating certain Galois groups. In this case, I use the magma online instead
def magma_free_is_abelian(K):
    sfbase = str(K.base_field().defining_polynomial())
    sr = str(K.base_field().gen())
    sgbase = str(K.defining_polynomial())
    a = magma_free('R<x> := PolynomialRing(RationalField());M<'+sr+'> := NumberField('+sfbase+');R<x> := PolynomialRing(M);K:=NumberField('+sgbase+');IsAbelian(GaloisGroup(K));')
    if a.format() == 'false':
        return False
    if a.format() == 'true':
        return True
    raise RuntimeError(a.format())

# the same as above, but returns the exponent of the galois group of K
def magma_free_exponent(K):
    sfbase = str(K.base_field().defining_polynomial())
    sr = str(K.base_field().gen())
    sgbase = str(K.defining_polynomial())
    a = magma_free('R<x> := PolynomialRing(RationalField());M<'+sr+'> := NumberField('+sfbase+');R<x> := PolynomialRing(M);K:=NumberField('+sgbase+');Exponent(GaloisGroup(K));')
    return ZZ(a.format())

# computes the symbol (alpha/q) that appears in, e.g. page 646 of [Nak04]
# this is what we call eta_q in the article
def norm_residue_symbol(alpha, q, K):
    if q.norm() % 2 == 0:
        raise RuntimeError('q cannot be a prime over 2')
    if q.is_coprime(K.ideal(alpha)) == False:
        raise RuntimeError('alpha and q are not coprime')
    Kq = K.residue_field(q)
    return 1 if Kq(alpha).is_square() else -1 

# this is the phi0 of conductor q as defined on [Nak04] p.646
# if q is over a prime which is -1 mod 4 then this is (alpha/q)·alpha
# if q is over 2, this is eta_minus_8(alpha)·alpha, cf. page 642 of [Nak04]
def phi0(alpha, q, K): 
    if q.norm() % 4 == 1:
        raise RuntimeError('q cannot be 1 mod 4 in phi_0')
    if q.norm() % 4 == 3:
        return norm_residue_symbol(alpha, q, K) * alpha
    else:
        return eta_minus_8(alpha, K) * alpha

# If phi is a hecke character and P is an ideal in K, we compute phi(P) + phi(\bar P), as in p. 647 of [Nak04]
# The caracter can be of the form phi0*eta_a * eta_b *eta_c, were a,b are assummed to be odd and c is either -4, 8 or -8 (and it can happen that they are not all present)
# w1 = [a, b] means that the character contains eta_a*eta_b
# w2 can be either 4 or 8, meaning that it is either eta_{-4} or eta_{-8}
def phi_plus_phi_conj(P, q, K, w1 = [], w2 = []):
    assert len((P^2).gens_reduced()) == 1
    alpha = (P^2).gens_reduced()[0]
    x2 = phi0(alpha, q, K)
    xxbar = phi0(K(P.norm()), q, K)
    for a in w1 + w2:
        if a == -4:
            xxbar *= eta_minus_4(K(P.norm()), K)
            x2 *= eta_minus_4(alpha, K)
        elif a == 8:
            xxbar *= eta_8(K(P.norm()), K)
            x2 *= eta_8(alpha, K)
        elif a == -8:
            xxbar *= eta_minus_8(K(P.norm()), K)
            x2 *= eta_minus_8(alpha, K)
        else: # case l odd
            assert norm_residue_symbol(-1, K.ideal(a).factor()[0][0], K) == (-1)^((a-1)/2)
            xxbar *= norm_residue_symbol(K(P.norm()), K.ideal(a).factor()[0][0], K)
            x2 *= norm_residue_symbol(alpha, K.ideal(a).factor()[0][0], K) 
    assert not x2.is_square()
    R.<y> = PolynomialRing(K)
    Wa.<rx2a> = NumberField(y^2 - x2, 'rx2').absolute_field()
    x = rx2a
    x2_1 = K.embeddings(Wa)[0](x2)
    xxbar_1 = K.embeddings(Wa)[0](xxbar)
    x2_2 = K.embeddings(Wa)[1](x2)
    xxbar_2 = K.embeddings(Wa)[1](xxbar)
    z = (x2_1 + xxbar_1)/x
    if z.minpoly().degree() > 2: # try if it is with the other embedding
        # print 'trying the other embedding'
        z = (x2_2 + xxbar_2)/x 
    if z.minpoly().degree() > 2:
        # we check that phi(P) + phi(\bar P) lies in a quadratic, otherwise something is wrong
        raise RuntimeError('phi(P) + phi(\bar P) is not a quadratic number')
    return z

# Returns P1 and P2, two generators of the class group of K. We check that phi0_plus_phi0_conj(Pi) are quadratic numbers
def find_P1_P2(q, K, min_prime = 1): 
    D = K.discriminant()
    p = 1
    Ps = []
    while True:
        p = p.next_prime()
        if kronecker_symbol(D, p) != 1:
            continue
        if p < min_prime: 
            print 'changing prime in D =',D
            continue
        P = K.ideal(p).factor()[0][0]
        if P.is_principal():
            continue
        if len(Ps) > 0:
            if (Ps[0]*P^-1).is_principal():
                continue
        try:
            phi_plus_phi_conj(P, q, K)
        except RuntimeError:
            # assert 0 #this shouldn't happen
            continue
        Ps.append(P)
        if len(Ps) == 2:
            return Ps[0], Ps[1]

# finds n as in Proposition 7 of [Nak04]
def find_n(P, Q, K, w1 = [], w2 = []): 
    s = phi_plus_phi_conj(P, Q, K, w1, w2)
    # print 'in find_n the degree of the minimal polynomial is ', s.minpoly().degree()
    n = s.minpoly().discriminant().squarefree_part()
    return n

# find if one of the quaternion algebras (p1s,p2s), (p1s, p1s·p2s) or (p2s, p1s·p2s) is split
def is_there_a_split_algebra(p1s, p2s):
    invariants = -1
    for invs in [[p1s, p2s], [p1s, p1s*p2s], [p2s, p1s*p2s]]:
        if QuaternionAlgebra(invs[0], invs[1]).discriminant() == 1:
            invariants = invs
            return invariants
    return invariants

# If is_there_a_split_algebra(p1s, p2s) does not work, we need to do the same but with quaternion algebras over K rather than over Q
def find_p1_p2(D):
    f = D.factor()
    if f[0][0] == 2:
        p1 = f[1][0]
        p2 = f[2][0]
        p1s = p1 if p1 % 4 == 1 else -p1 
        p2s = p2 if p2 % 4 == 1 else -p2
        if is_there_a_split_algebra(p1s, p2s) == -1:
            raise RuntimeError('there seems to be no split quaternion algebra')
        return p1, p2, p1s, p2s
    else:
        found = False
        for p1, p2 in [[f[0][0], f[1][0]], [f[0][0], f[2][0]], [f[1][0], f[2][0]]]:
            p1s = p1 if p1 % 4 == 1 else -p1 
            p2s = p2 if p2 % 4 == 1 else -p2 
            if is_there_a_split_algebra(p1s, p2s) != -1:
                return p1, p2, p1s, p2s
        raise RuntimeError('there seems to be no split quaternion algebra')

def eta_minus_4(alpha, K):
    D = K.discriminant()
    assert D % 2 == 0
    m = D/4
    assert m.is_integer()
    m = ZZ(m)
    assert m % 2 == 1
    a = K.ideal(2).factor()[0][0].gens_reduced()[1] # generates the prime above 2
    f = a.minpoly() # Eisenstein polynomial such that Q_2[x]/(f) = K_2
    f_magma = magma(f)
    R = magma('pAdicRing(2,100)')
    OK2 = R.TotallyRamifiedExtension(f_magma) # This is the completion of OK at the prime above 2
    rm = OK2(m).SquareRoot()
    alpha = (magma(alpha.minpoly())).Roots(OK2)[1][1] # we need to view alpha in OK2
    for z in [1, 5, 3 - 2*rm, 5*(3-2*rm)]:
        if (alpha/z).IsSquare():
            return 1
    assert any((rm*alpha*w).IsSquare() for w in [1, 5, 3 - 2*rm, 5*(3-2*rm)]) # this has to be true if U_2/U_2^2 is generated by [rm, 3 - 2*rm, 5]
    return -1

def eta_minus_8(alpha, K):
    D = K.discriminant()
    assert D % 2 == 0
    m = D/4
    assert m.is_integer()
    m = ZZ(m)
    assert m % 2 == 0
    a = K.ideal(2).factor()[0][0].gens_reduced()[1] # generates the prime above 2
    f = a.minpoly() # Eisenstein polynomial such that Q_2[x]/(f) = K_2
    f_magma = magma(f)
    R = magma('pAdicRing(2,100)')
    OK2 = R.TotallyRamifiedExtension(f_magma) # This is the completion of OK at the prime above 2
    rm = OK2(m).SquareRoot()
    alpha = (magma(alpha.minpoly())).Roots(OK2)[1][1] # we need to view alpha in OK2
    for z in [1, 1+rm, -5, -5*(1+rm)]:
        if (alpha/z).IsSquare():
            return 1
    assert any((-1*alpha*w).IsSquare() for w in [1, 1+rm, -5, -5*(1+rm)]) # this has to be true if U_2/U_2^2 is generated by [1 + rm, -1, 5]
    return -1

def eta_8(alpha, K):
    D = K.discriminant()
    assert D % 2 == 0
    m = D/4
    assert m.is_integer()
    m = ZZ(m)
    assert m % 2 == 0
    a = K.ideal(2).factor()[0][0].gens_reduced()[1] # generates the prime above 2
    f = a.minpoly() # Eisenstein polynomial such that Q_2[x]/(f) = K_2
    f_magma = magma(f)
    R = magma('pAdicRing(2,100)')
    OK2 = R.TotallyRamifiedExtension(f_magma) # This is the completion of OK at the prime above 2
    rm = OK2(m).SquareRoot()
    alpha = (magma(alpha.minpoly())).Roots(OK2)[1][1] # we need to view alpha in OK2
    for z in [1, 1+rm, -1, -1*(1+rm)]:
        if (alpha/z).IsSquare():
            return 1
    assert any((5*alpha*w).IsSquare() for w in [1, 1+rm, -1, -1*(1+rm)]) # this has to be true if U_2/U_2^2 is generated by [1 + rm, -1, 5]
    return -1


# this is the main routine: given a field K with class group C2 x C2 it computes the endomorphism algebras of the restriction of scalars of the eight classes of Q-curves over that field
# set magma_free = True for doing the computations of the Galois groups using the magma online, instead of the local magma
# min_prime is mainly for debugging purposes   
def compute_endomorphism_algebras(D, use_magma_free = False, min_prime = 1):
    # print '####################'
    # print "Field of Discriminant D = ", D, " = ", D.factor()
    x = QQ['x'].gen()
    K.<r> = NumberField(x^2 - D)
    f = D.factor()
    # first we find the conductor Q of the character phi_0. If there is a q | D which is 3 mod 4 we take Q to be the prime above q. If not, we take Q to be the prime above 2 and then phi_0 will be eta_minus_8
    found = False
    for q in f: 
        if q[0] % 4 == 3:
            Q = K.ideal(q[0]).factor()[0][0]
            # print "Using phi_0 = eta_",q[0]
            found = True
            break
    if found == False:
        if D % 2 == 0:
            Q = K.ideal(2).factor()[0][0]
            # print 'Using phi_0 = eta_{-8}'
    try:
        p1, p2, p1s, p2s = find_p1_p2(D)
    except RuntimeError:
        p1 = -1; p2 = -1
        fa = D.factor()
        if fa[1][0] % 4 == 1:
            p1 = fa[1][0]; p1s = p1
            p2 = fa[2][0]; p2s = p2 if p2 % 4 == 1 else -p2
        elif fa[2][0] % 4 == 1:
            p1 = fa[2][0]; p1s = p1
            p2 = fa[1][0]; p2s = -p2
        if p1 == -1 or p2 == -1:
            raise RuntimeError('There is no split quaternion algebra, and we cannot find p1 and p2 as in Nakamura p. 639')
    R.<y> = PolynomialRing(K)
    H.<a,b> = NumberFieldTower([y^2 - p1s, y^2-p2s])
    assert H.absolute_field('hh').is_isomorphic(K.hilbert_class_field('rr').absolute_field('rr'))
    P1, P2 = find_P1_P2(Q,K, min_prime) # these two generate Cl(K) and we have found them so that phi_0_plus_phi0_conj is a quadratic irrationality
    for qq in [p1s, p2s, p1s*p2s]:
        K1.<g1> = NumberField(y^2 - qq)
        if len(K1.ideal(P1).factor()) == 2:
            q1 = qq
        if len(K1.ideal(P2).factor()) == 2:
            q2 = qq
    L1.<g1> = NumberField(y^2 - q1) # field fixed by the decomposition group at P1 
    L2.<g2> = NumberField(y^2 - q2) # field fixed by the decomposition group at P2
    # print 'L1 =', L1
    # print 'L2 =', L2
    F1 = L1.maximal_totally_real_subfield()[0]
    F2 = L2.maximal_totally_real_subfield()[0]
    x = QQ['x'].gen()
    f = non_abelian_extensions[D]
    k0H.<gk0H> = NumberField(f) 
    # k0H, which is a quadratic extension of H which non abelian over K
    assert k0H.is_galois()
    k_K.<gkK> = k0H.relativize(K.embeddings(k0H)[0])
    if not use_magma_free:
        assert magma(k_K).GaloisGroup().IsAbelian().sage() == False
    else:
        assert magma_free_is_abelian(k_K) == False
    # assert magma(k_K).GaloisGroup().IsAbelian().sage() == False
    for S in k0H.subfields():
        if S[0].is_isomorphic(L1):
            LL1.<g> = k0H.relativize(S[1]) # LL1 is the relative field extension k0H/S[0], where S[0] is the subfield of k0H isomorphic to L1
        if S[0].is_isomorphic(L2):
            LL2.<g> = k0H.relativize(S[1])
        if S[0].is_isomorphic(F1):
            FF1.<g> = k0H.relativize(S[1])
        if S[0].is_isomorphic(F2):
            FF2.<g> = k0H.relativize(S[1])
    w1s, w2s = find_w1s_w2s(D)
    # print w1s
    # print w2s
    a1,b1= find_n(P1, Q, K, w1 = w1s[0], w2=w2s[0]), find_n(P2, Q, K, w1 = w1s[0], w2=w2s[0])
    a2,b2= find_n(P1, Q, K, w1 = w1s[1], w2=w2s[1]), find_n(P2, Q, K, w1 = w1s[1], w2=w2s[1])
    a3,b3= find_n(P1, Q, K, w1 = w1s[2], w2=w2s[2]), find_n(P2, Q, K, w1 = w1s[2], w2=w2s[2])
    a4,b4= find_n(P1, Q, K, w1 = w1s[3], w2=w2s[3]), find_n(P2, Q, K, w1 = w1s[3], w2=w2s[3])
    # print 'Quaternion Algebras'
    a5 = compute_T(LL1, FF1, P1, Q, K, w1 = w1s[0], w2=w2s[0], use_magma_free = use_magma_free); b5 = compute_T(LL2, FF2, P2, Q, K,w1 = w1s[0], w2=w2s[0],use_magma_free = use_magma_free); # print a5, b5, 'Disc =', QuaternionAlgebra(a5,b5).discriminant(),QuaternionAlgebra(a5,b5).discriminant() == 1; 
    D5 = QuaternionAlgebra(a5,b5).discriminant()
    a6= compute_T(LL1, FF1, P1, Q, K,w1 = w1s[1], w2=w2s[1],use_magma_free = use_magma_free); b6 =  compute_T(LL2, FF2, P2, Q, K, w1 = w1s[1], w2=w2s[1],use_magma_free = use_magma_free); # print a6, b6,  'Disc =', QuaternionAlgebra(a6,b6).discriminant(), QuaternionAlgebra(a6,b6).discriminant() == 1  ; 
    D6 = QuaternionAlgebra(a6,b6).discriminant()
    a7 = compute_T(LL1, FF1, P1, Q, K, w1 = w1s[2], w2=w2s[2],use_magma_free = use_magma_free); b7 = compute_T(LL2, FF2, P2, Q, K, w1 = w1s[2], w2=w2s[2],use_magma_free = use_magma_free); #print a7, b7,  'Disc =', QuaternionAlgebra(a7,b7).discriminant(),QuaternionAlgebra(a7,b7).discriminant() == 1; 
    D7 =  QuaternionAlgebra(a7,b7).discriminant()
    a8 = compute_T(LL1, FF1, P1, Q, K, w1 = w1s[3], w2=w2s[3],use_magma_free = use_magma_free); b8 = compute_T(LL2, FF2, P2, Q, K, w1 = w1s[3], w2=w2s[3],use_magma_free = use_magma_free); # print a8, b8,  'Disc =', QuaternionAlgebra(a8,b8).discriminant(), QuaternionAlgebra(a8,b8).discriminant() == 1; 
    D8 = QuaternionAlgebra(a8,b8).discriminant()
    # We print the table, in latex format
    print '\\hline'
    print '$'+D.str()+'$' + ' & $(' + a1.str() + ',' + b1.str() + '),('+a2.str()+','+b2.str()+'),('+a3.str()+','+b3.str()+'),('+a4.str() +','+b4.str()+')$& $'+D5.str()+','+D6.str()+','+D7.str()+','+D8.str()+'$\\\\'

# this finds the elements of W/W_0. A basis is what we call in the paper \tilde\omega_1 and \tilde\omega_2
# the output are two vectors w1 and w2, and this means that the characters of W/W0 are w1[0]·w2[0], w1[1]·w2[1], w1[2]·w2[2] and w1[3]·w2[3]. Each wi[j] can be either empty (which represents the trivial character), or a vector of integers which means that wi[j] is the product of "eta" characters associated to these integers.
# These are the 6 items in p. 15 of [FG18]
def find_w1s_w2s(D):
    a, b, c = D.factor()
    if a[0] == 2  and a[1] == 2:
        if b[0] % 4 == 3 and c[0] % 4 == 3:
            w1 = [[], [b[0],c[0]], [], [b[0],c[0]]]
            w2 = [[], [], [-4], [-4]]
            return [w1, w2]
    if a[0] % 2 == 1:
        ones = [z for z in [a, b, c] if z[0]%4 == 1]
        if len(ones) == 2:
            b, c = ones
            w1 = [[], [b[0]], [], [b[0]]]
            w2 = [[], [], [c[0]], [c[0]]]
            return [w1, w2]
        if len(ones) == 0:
            w1 = [[], [a[0], b[0]], [], [a[0], b[0]]]
            w2 = [[], [], [a[0], c[0]], [a[0], c[0]]]
            return [w1, w2]
    if a[0] == 2 and a[1] == 3:
        if b[0] % 4 == 3 and c[0] % 4 == 3:
            w1 = [[], [-8,b[0]], [], [-8,b[0]]]
            w2 = [[], [], [-8,c[0]], [-8,c[0]]]
            return [w1, w2]
        if b[0] % 4 == 3 and c[0] % 4 == 1:
            w1 = [[], [8], [], [8]]
            w2 = [[], [], [c[0]], [c[0]]]
            return [w1, w2]
        if c[0] % 4 == 3 and b[0] % 4 == 1:
            w1 = [[], [8], [], [8]]
            w2 = [[], [], [b[0]], [b[0]]]
            return [w1, w2]
        if  b[0] % 4 == 1 and c[0] % 4 == 1:
            w1 = [[], [b[0]], [], [b[0]]]
            w2 = [[], [], [c[0]], [c[0]]]
            return [w1, w2]
    raise NotImplementedError('no omegas yet for D of this form')

# This is used in computing the quaternion endomorphism algebra (t1, t2)_Q. Here we compute the ti associated to the prime P. The field L is the decomposition group of H at P and F is the totally real subfield. 
def compute_T(L, F, P, Q, K, w1 = [], w2 = [], use_magma_free = False):
    D = K.discriminant()
    n = find_n(P, Q, K, w1, w2)
    # For these three discriminants my local version of returns an error when trying to compute the Galois group, so I use the magma calculator online instead
    if not use_magma_free:
        Fabelian = magma(F).GaloisGroup().IsAbelian()
    else:
        Fabelian = magma_free_is_abelian(F)
    if not use_magma_free:
        exponent = magma(L).GaloisGroup().Exponent()
    else:
        exponent = magma_free_exponent(L)
    if exponent == 2:
        if Fabelian:
            return n.squarefree_part()
        else:
            return (D/n).squarefree_part()
    else:
        if Fabelian:
            return (-n).squarefree_part()
        else:
            return (-D/n).squarefree_part()
    
# To reproduce Table 1 of [FG18], uncomment the following bunch of code and execute 
# sage: %runfile nakamura.sage

# for i in range(len(data)):
#     D = data[i][1]
#     if D != - 715:
#         use_magma_free = False
#     else:
#         use_magma_free = True
#     try:
#         compute_endomorphism_algebras(D, use_magma_free = use_magma_free)
#     except RuntimeError as e:
#         print e.args
#     except NotImplementedError as e:
#         print e.args
#     except TypeError as e:
#         print e.args


# # to compute the endomorphism algebras for an individual discriminant, you can run this
# D = -195
# compute_endomorphism_algebras(D, use_magma_free = False)


# References

# [FG18] Francesc Fité, Xavier Guitart, Endomorphism algebras of geometrically split abelian surfaces over Q.
# [Nak04] Tetsuo Nakamura, A classification of Q-curves with complex multiplication, J. Math. Soc. Japan, Vol 56, No 2, 2004.

